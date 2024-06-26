use cgmath::Vector3;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use spatial_hash_3d::*;

#[derive(Debug)]
pub struct Data {
    some_data: i32,
}

impl Default for Data {
    fn default() -> Self {
        Data { some_data: 0 }
    }
}

fn create_and_fill(x: i32, y: i32, z: i32) -> SpatialHashGrid<Data> {
    let mut sh: SpatialHashGrid<Data> =
        SpatialHashGrid::new(x as i32, y as i32, z as i32, Data::default);
    let mut count = 0;
    for (i, j, k) in itertools::iproduct!(0..x, 0..y, 0..z) {
        let pos = Vector3::new(i, j, k);
        sh[pos] = Data { some_data: count };
        count += 1;
    }
    sh
}

/// Creates random bounding boxes within x,y,z size
fn generate_bounding_box(
    rng: &mut SmallRng,
    x: i32,
    y: i32,
    z: i32,
) -> (Vector3<i32>, Vector3<i32>) {
    let min = Vector3::new(
        rng.gen_range(0..(x - 2)),
        rng.gen_range(0..(y - 2)),
        rng.gen_range(0..(z - 2)),
    );
    let max = Vector3::new(
        rng.gen_range(min.x..x),
        rng.gen_range(min.y..y),
        rng.gen_range(min.z..z),
    );
    if min.x > max.x || min.y > max.y || min.z > max.z {
        panic!("Generated volume is not in this Universe");
    }
    (min, max)
}

fn bench_get_filled_data(sh: &SpatialHashGrid<Data>, min: Vector3<i32>, max: Vector3<i32>) {
    for (c, elem) in sh.iter_cubes(min, max) {
        black_box(c);
        black_box(elem);
    }
}

fn bench_modify_filled_data(sh: &mut SpatialHashGrid<Data>, min: Vector3<i32>, max: Vector3<i32>) {
    for (c, idx, elem) in sh.iter_cubes_mut(min, max) {
        elem.some_data += c.x;
        black_box(idx);
    }
}

/// Measures how quickly the data is retrieved from the structure
/// Two tests inside - one for mutable and one for immutable iteration
pub fn bench_get_data_if_there(c: &mut Criterion) {
    let mut rng = SmallRng::seed_from_u64(42);

    let mut group = c.benchmark_group("lookups");

    for size in [5i32, 10, 20] {
        group.bench_with_input(
            criterion::BenchmarkId::from_parameter(size),
            &size,
            |b, &size| {
                //generate max border values for the base volume, Max value for each axis is never larger than 20
                let (x, y, z) = (size, size, size);
                //generate bounding volume based on the previous values, each value is never larger than "max border values"

                //fill general space
                let spatial = create_and_fill(x, y, z);

                b.iter(|| {
                    let (min, max) = generate_bounding_box(&mut rng, x, y, z);
                    //bounding box is located in general space, look for the data in bounding box
                    bench_get_filled_data(&spatial, min, max);
                })
            },
        );
    }
    drop(group);
    let mut group = c.benchmark_group("edits");

    for size in [5i32, 10, 20] {
        group.bench_with_input(
            criterion::BenchmarkId::from_parameter(size),
            &size,
            |b, &size| {
                //generate max border values for the base volume, Max value for each axis is never larger than 20
                let (x, y, z) = (size, size, size);
                //generate bounding volume based on the previous values, each value is never larger than "max border values"

                //fill general space
                let mut spatial = create_and_fill(x, y, z);

                // println!("General space {:?}, {:?}, {:?}", x, y, z);
                // println!("Min={:?}, Max={:?}", min, max);

                b.iter(|| {
                    let (min, max) = generate_bounding_box(&mut rng, x, y, z);
                    //bounding box is located in general space, look for the data in bounding box
                    bench_modify_filled_data(&mut spatial, min, max);
                    black_box(&spatial);
                })
            },
        );
    }
}

/// Measures how quickly the data is filled in the structure
/// Should be pretty fast if size of D is small

pub fn bench_fill_data(c: &mut Criterion) {
    let mut group = c.benchmark_group("writes");
    for size in [5i32, 10, 20] {
        group.bench_with_input(
            criterion::BenchmarkId::from_parameter(size),
            &size,
            |b, &size| {
                b.iter(|| {
                    let spatial = create_and_fill(size, size, size);
                    black_box(spatial);
                })
            },
        );
    }
}

criterion_group!(benches, bench_get_data_if_there, bench_fill_data);
criterion_main!(benches);
