# Cable

[![Crate](https://img.shields.io/crates/v/rand.svg)](https://crates.io/crates/rand)

A `cable`(pointer) with a `hook`(header at address) at the end and a sized `payload`(array)
### Features
A pointer type for heap allocation, with some special features:
- Stores an optional user specified header at address
- Stashes the size of the data inline
- A resizable array with bounds checking that requires just a pointer to use
Adds padding where necessary to maintain alignment for size and elements. 
## Usage
Add this to your `Cargo.toml`:
```toml
[dependencies]
cable = "0.1.1"
```
## Examples
```
let mut data: Cable<f64, (i32, i32, i32, i32)> = Cable::with_capacity_zeroed(8, (1, 2, 3, 4));
data[0] = 1.0;
data[1] = 6.0;
data[2] = 9.0;
for i in data.iter() {
    println!("{:?}", i);
}
println!("Header: {:?}", data.header().unwrap());
println!("Footprint: {}", data.footprint());
```
The `Cable<T, H>` is useful in creating other heap objects.
Creating a simple dynamic storage with a length and capacity:
```
let mut data: Cable<i32, usize> = Cable::with_capacity(24, 6); // allocate capacity for 24 elements
data[0] = 19;
data[1] = 22;
data[2] = 35;
data[3] = 53;
data[4] = 68;
data[5] = 13;
println!("Length: {}", data.header().unwrap());
println!("Footprint: {}", data.footprint());
```
The `Cable<T, H>` works well for nested structures when a small footprint is required:
```
let mut x: Vec<Cable<i32>> = Vec::with_capacity(24);
x.push(Cable::with_capacity(2));
x[0][0] = 67;
x[0][1] = 45;
x.push(Cable::with_capacity(8));
x[1][2] = 32;
x[1][5] = 19;
```
In this case the vector acts like a 2D array but each element can have a variable size.
This allows for compact data structures with proper bounds checking and a minimal footprint.
A struct can be used as a header for convenience:
```
struct Info {
    id: i32,
    position: (f32, f32),
    length: usize,
}

let mut x: Cable<i32, Info> = Cable::with_capacity(
    24,
    Info {
        id: -1,
        position: (0.0, 0.0),
        length: 0,
    },
);
```
A header may be omitted for brevity:
```
let mut x: Cable<i32> = Cable::new();
```
## Safety
This pointer is safe as it always allocates at least `mem::size_of::<usize>()` bytes on the heap and will point to that allocation.
## Allocation
A cable has some special allocation features and considerations:
- Will allocate at least `mem::size_of::<H>()` + padding for `usize` + `mem::size_of::<usize>()` + padding for `T`.
- H can be zero-sized, in this case, such as when using the unit type `H = ()` the header is not allocated.
- Can optionally allocate memory zeroed.
- Cost is minimal, most memory layout is determined at compile time.
- Resembles a `Box<H>` when payload is unallocated (although with an extra `mem::size_of::<usize>()` bytes, see `into_boxed_header`).
## Crate features
To be determined, will likely support in the future:
- 'no-std'
- 'serde'
- 'custom allocator'
