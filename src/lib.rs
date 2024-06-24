#![doc = include_str!("../README.md")]

use itertools::{ConsTuples, Product};
use std::fmt::{Debug, Formatter};
use std::ops::RangeInclusive;

#[cfg(feature = "cgmath")]
type Vector3i = cgmath::Vector3<i32>;

#[cfg(feature = "godot")]
type Vector3i = godot::builtin::Vector3i;

#[cfg(all(feature = "godot", feature = "cgmath"))]
compile_error!("enable either `godot` or `cgmath` feature, not both");

type BackingStorage<D> = Vec<D>;

/// Spatial hash data structure. see crate docs for usage.
pub struct SpatialHashGrid<D: Sized> {
    dims: Vector3i,
    cubes: BackingStorage<D>,
}

#[inline]
/// Converts position in a spatial hash of given dimensions into an index. If position is not in dimensions, returns None.
fn pos_to_index(dims: Vector3i, v: Vector3i) -> Option<i32> {
    let (x, y, z) = (v.x as i32, v.y as i32, v.z as i32);
    if (x >= dims.x) || (y >= dims.y) || (z >= dims.z) {
        return None;
    }
    Some(x + y * dims.x + z * (dims.x * dims.y))
}

impl<D: Sized> SpatialHashGrid<D> {
    /// x,y,z set the dimentsions, filler is a function that is used to initialize contents.
    pub fn new<V>(x: i32, y: i32, z: i32, filler: V) -> Self
    where
        V: FnMut() -> D,
    {
        let cap = (x * y * z) as usize;
        // allocate memory
        let mut d = Vec::with_capacity(cap);
        // initialize elements
        d.resize_with(cap, filler);
        Self {
            dims: Vector3i::new(x, y, z),
            cubes: d,
        }
    }

    /// Get the size/bounds of the area under spatial hash.
    #[inline]
    pub fn size(&self) -> Vector3i {
        self.dims
    }

    /// Safely retrieve element by index, will do runtime OOB checks
    #[inline(always)]
    pub fn get_mut(&mut self, idx: usize) -> Option<&mut D> {
        self.cubes.get_mut(idx)
    }

    /// Safely retrieve element by index, will do runtime OOB checks
    #[inline(always)]
    pub fn get(&mut self, idx: usize) -> Option<&D> {
        self.cubes.get(idx)
    }

    #[inline]
    /// Convert given position into index in this spatial hash grid
    pub fn pos_to_index(&self, v: Vector3i) -> Option<i32> {
        pos_to_index(self.dims, v)
    }
    ///Iterate over cube indices in given bounds [min, max]
    #[inline]
    pub fn iter_cube_indices(&self, min: Vector3i, max: Vector3i) -> BoxIdxIterator {
        BoxIdxIterator {
            dims: self.dims,
            iter: itertools::iproduct!(min.x..=max.x, min.y..=max.y, min.z..=max.z),
        }
    }

    ///Iterate over cubes in given bounds [min, max] inside the main cube in read only state
    #[inline]
    pub fn iter_cubes(&self, min: Vector3i, max: Vector3i) -> BoxIterator<D> {
        BoxIterator {
            data: &self.cubes,
            iter: self.iter_cube_indices(min, max),
        }
    }
    ///Iterate over cubes in given bounds [min, max] in read and write state.
    #[inline]
    pub fn iter_cubes_mut(&mut self, min: Vector3i, max: Vector3i) -> BoxIteratorMut<D> {
        let inner_iter = self.iter_cube_indices(min, max);
        BoxIteratorMut {
            data: &mut self.cubes,
            iter: inner_iter,
        }
    }
}

impl<D: Debug> Debug for SpatialHashGrid<D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "<SpatialHashGrid {}x{}x{}:",
            self.dims.x, self.dims.y, self.dims.z
        )?;
        for z in 0..self.dims.z {
            writeln!(f, "#Slice z={}:", z)?;
            for x in 0..self.dims.x {
                for y in 0..self.dims.y {
                    let v = Vector3i::new(x as i32, y as i32, z as i32);
                    let idx = self.pos_to_index(v).expect("This can not go wrong");
                    write!(f, "{:?}, ", &self.cubes[idx as usize])?;
                }
                writeln!(f)?; // finish row in a slice
            }
        }
        write!(f, ">")
    }
}

pub struct BoxIdxIterator {
    dims: Vector3i,
    #[allow(clippy::type_complexity)]
    iter: ConsTuples<
        Product<Product<RangeInclusive<i32>, RangeInclusive<i32>>, RangeInclusive<i32>>,
        ((i32, i32), i32),
    >,
}

impl Iterator for BoxIdxIterator {
    type Item = (Vector3i, usize);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (x, y, z) = self.iter.next()?;
            let c = Vector3i { x, y, z };
            let idx = match pos_to_index(self.dims, c) {
                Some(idx) => idx,
                None => {
                    continue;
                }
            } as usize;
            return Some((c, idx));
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_min, max) = self.iter.size_hint();
        (0, max)
    }
}

pub struct BoxIterator<'a, D: Sized> {
    data: &'a BackingStorage<D>,
    iter: BoxIdxIterator,
}
impl<'a, D: Sized> BoxIterator<'a, D> {
    ///Morph into a BoxIterator which also returns index of elements it traverses.
    pub fn with_index(self) -> BoxIteratorWithIndex<'a, D> {
        BoxIteratorWithIndex {
            data: self.data,
            iter: self.iter,
        }
    }
}

impl<'a, D: Sized> Iterator for BoxIterator<'a, D> {
    type Item = (Vector3i, &'a D);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let (pos, idx) = self.iter.next()?;
        let d = self.data.get(idx);
        Some((pos, d.unwrap()))
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_min, max) = self.iter.size_hint();
        (0, max)
    }
}

pub struct BoxIteratorWithIndex<'a, D: Sized> {
    data: &'a BackingStorage<D>,
    iter: BoxIdxIterator,
}

impl<'a, D: Sized> Iterator for BoxIteratorWithIndex<'a, D> {
    type Item = (Vector3i, usize, &'a D);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let (pos, idx) = self.iter.next()?;
        let d = self.data.get(idx);
        Some((pos, idx, d.unwrap()))
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_min, max) = self.iter.size_hint();
        (0, max)
    }
}

pub struct BoxIteratorMut<'a, D: Sized> {
    data: &'a mut BackingStorage<D>,
    iter: BoxIdxIterator,
}

impl<'a, D: Sized> Iterator for BoxIteratorMut<'a, D> {
    type Item = (Vector3i, usize, &'a mut D);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let (pos, idx) = self.iter.next()?;
        // Need unsafe block to return mutable references here.
        unsafe {
            //SAFETY: the index position should be valid since pos_to_index can
            //not return invalid position.
            let d = self.data.get_unchecked_mut(idx) as *mut D;
            // SAFETY: we know this can not possibly point to anything invalid
            // We also know that the returned reference should not outlive the iterator
            // unless user does "something really terrible"(tm)
            return Some((pos, idx, d.as_mut().unwrap_unchecked()));
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_min, max) = self.iter.size_hint();
        (0, max)
    }
}

impl<D: Sized> std::ops::Index<Vector3i> for SpatialHashGrid<D> {
    type Output = D;
    /// Retrieve reference to element by position
    #[inline]
    fn index(&self, index: Vector3i) -> &Self::Output {
        let i = self.pos_to_index(index).expect("Index out of bounds");
        self.cubes.index(i as usize)
    }
}

impl<D: Sized> std::ops::IndexMut<Vector3i> for SpatialHashGrid<D> {
    /// Retrieve mutable reference to element by position
    #[inline]
    fn index_mut(&mut self, index: Vector3i) -> &mut Self::Output {
        let i = self.pos_to_index(index).expect("Index out of bounds");
        self.cubes.index_mut(i as usize)
    }
}

impl<D: Sized> std::ops::Index<usize> for SpatialHashGrid<D> {
    type Output = D;
    /// Retrieve reference to element by index
    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        self.cubes.index(index)
    }
}

impl<D: Sized> std::ops::IndexMut<usize> for SpatialHashGrid<D> {
    /// Retrieve mutable reference to element by index
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.cubes.index_mut(index)
    }
}

#[cfg(test)]
mod tests {
    use crate::SpatialHashGrid;
    use cgmath::Vector3;

    #[derive(Debug, Clone)]
    pub struct Data {
        x: i32,
        y: i32,
        z: i32,
    }

    impl Default for Data {
        fn default() -> Self {
            Data { x: 0, y: 0, z: 0 }
        }
    }

    #[test]
    fn test_iter_cubes_mut() {
        let mut sh: SpatialHashGrid<i32> = SpatialHashGrid::new(5, 5, 5, i32::default);

        let sx = 3;
        let sy = 4;
        let sz = 5;
        for (i, j, k) in itertools::iproduct!(0..sx, 0..sy, 0..sz) {
            let pos = Vector3::new(i, j, k);
            sh[pos] = 1;
        }

        let min = Vector3::new(0, 0, 0);
        let b = Vector3::new(2, 1, 2);
        let max = Vector3::new(sx, sy, sz);

        for (_p, _i, d) in sh.iter_cubes_mut(min, b) {
            *d += 1;
        }

        let mut count = 0;
        for (_p, d) in sh.iter_cubes(min, max) {
            count += *d;
        }
        assert_eq!(
            count,
            (sx * sy * sz) + (b.x + 1) * (b.y + 1) * (b.z + 1),
            "Incorrect sum of values"
        );
        let mut count = 0;
        for (p, idx, d) in sh.iter_cubes(min, max).with_index() {
            assert_eq!(
                sh.pos_to_index(p).expect("position should be valid"),
                idx as i32
            );
            count += *d;
        }
        assert_eq!(
            count,
            (sx * sy * sz) + (b.x + 1) * (b.y + 1) * (b.z + 1),
            "Incorrect sum of values"
        );
    }
    #[test]
    fn test_indexing() {
        let mut sh: SpatialHashGrid<Option<i32>> = SpatialHashGrid::new(5, 5, 5, || None);

        let p = Vector3 { x: 3, y: 3, z: 3 };
        sh[p] = Some(42);
        assert_eq!(sh[p], Some(42));
        sh[p] = None;
        assert_eq!(sh[p], None);
        println!("{:?}", sh);
    }
    #[test]
    fn test_debug_trait() {
        let mut sh: SpatialHashGrid<Data> = SpatialHashGrid::new(3, 3, 2, Data::default);
        let p = Vector3 { x: 1, y: 1, z: 1 };
        sh[p].x = 42;
        sh[p].y = 42;
        sh[p].z = 42;
        println!("{:?}", sh);
    }
}
