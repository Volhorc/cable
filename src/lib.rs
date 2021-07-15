use core::ptr::NonNull;
use std::alloc::Layout;
use std::marker::PhantomData;
use std::mem;
use std::ops;
use std::ptr;
use std::slice;

/// A pointer type for heap allocation that represents a block of memory.
/// Stores a user specified header(`H`) at address,
/// followed by the size of the allocation and
/// finally, a resizable array of `T`.
///
/// Adds padding where necessary.
///
/// # Examples
/// ```
/// let mut data: Cable<f64, (i32, i32, i32, i32)> = Cable::with_capacity_zeroed(8, (1, 2, 3, 4));
/// data[0] = 1.0;
/// data[1] = 6.0;
/// data[2] = 9.0;
///
/// for i in data.iter() {
///     println!("{:?}", i);
/// }
///
/// println!("Header: {:?}", data.header().unwrap());
/// println!("Footprint: {}", data.footprint());
/// ```
/// The `Cable<T, H>` is useful in creating other heap objects.
///
/// Creating a simple dynamic storage with a length and capacity:
/// ```
/// let mut data: Cable<i32, usize> = Cable::with_capacity(24, 6); // allocate capacity for 24 elements
/// data[0] = 19;
/// data[1] = 22;
/// data[2] = 35;
/// data[3] = 53;
/// data[4] = 68;
/// data[5] = 13;
///
/// println!("Length: {}", data.header().unwrap());
/// println!("Footprint: {}", data.footprint());
/// ```
/// The `Cable<T, H>` works well for nested structures when a small footprint is required:
/// ```
/// let mut x: Vec<Cable<i32>> = Vec::with_capacity(24);
/// x.push(Cable::with_capacity(2));
/// x[0][0] = 67;
/// x[0][1] = 45;
///
/// x.push(Cable::with_capacity(8));
/// x[1][2] = 32;
/// x[1][5] = 19;
/// ```
/// In this case the vector acts like a 2D array but each element can have a variable size.
/// This allows for compact data structures with proper bounds checking and a minimal footprint.
///
/// A struct can be used as a header for convenience:
/// ```
/// struct Info {
///     id: i32,
///     position: (f32, f32),
///     length: usize,
/// }
///
/// let mut x: Cable<i32, Info> = Cable::with_capacity(
///     24,
///     Info {
///         id: -1,
///         position: (0.0, 0.0),
///         length: 0,
///     },
/// );
/// ```
/// A header may be omitted for brevity:
/// ```
/// let mut x: Cable<i32> = Cable::new();
/// ```
///
/// # Safety
/// This pointer is safe as it always allocates at least `mem::size_of::<usize>()` bytes on the heap and will point to that allocation.
///
/// # Allocation
/// Will allocate at least `mem::size_of::<H>()` + padding for `usize` + `mem::size_of::<usize>()` + padding for `T`.
///
/// H can be zero-sized, in this case, such as when using the unit type `H = ()` the header is not allocated.
///
/// Can optionally allocate memory zeroed.
///
/// Cost is minimal, most memory layout is determined at compile time.
///
/// Resembles a `Box<H>` when payload is unallocated (although with an extra `mem::size_of::<usize>()` bytes, see `into_boxed_header`).
pub struct Cable<T, H = ()> {
    mem: NonNull<H>,
    phantom: PhantomData<T>,
}

// const version of max function
const fn max(a: usize, b: usize) -> usize {
    [a, b][(a < b) as usize]
}

// from std::alloc::Layout::padding_needed_for()
const fn pad(layout: Layout, align: usize) -> usize {
    let len = layout.size();
    let len_rounded_up = len.wrapping_add(align).wrapping_sub(1) & !align.wrapping_sub(1);
    len_rounded_up.wrapping_sub(len)
}

impl<T, H> Cable<T, H> {
    const SIZE_PADDING: usize = pad(Layout::new::<H>(), mem::align_of::<usize>());
    const HEADER_LAYOUT: Layout = unsafe {
        Layout::from_size_align_unchecked(
            mem::size_of::<H>() + Self::SIZE_PADDING + mem::size_of::<usize>(),
            max(mem::align_of::<H>(), mem::align_of::<usize>()),
        )
    };

    const PAYLOAD_PADDING: usize = pad(Self::HEADER_LAYOUT, mem::align_of::<T>());
    const BASE_LAYOUT: Layout = unsafe {
        Layout::from_size_align_unchecked(
            mem::size_of::<H>()
                + Self::SIZE_PADDING
                + mem::size_of::<usize>()
                + Self::PAYLOAD_PADDING,
            max(mem::align_of::<H>(), mem::align_of::<usize>()),
        )
    };

    /// Offset to capacity.
    const SIZE_OFFSET: isize = (mem::size_of::<H>() + Self::SIZE_PADDING) as isize;
    /// Offset to payload.
    const PAYLOAD_OFFSET: isize = (Self::BASE_LAYOUT.size()) as isize;

    /// `true` if the block has a valid header (non-zero-sized).
    const HEADER_EXISTS: bool = mem::size_of::<H>() != 0;
}

impl<T, H> Cable<T, H> {
    /// Constructs a new, empty `Cable<T>` on the heap with a size of `0`.
    /// The block will always allocate on the heap.
    ///
    /// Prefer `with_capacity`.
    ///
    /// # Safety
    /// This function is safe with zero-sized or unspecified headers.
    ///
    /// Memory for `header` will be initialized to zero if present.
    /// Only use this function if your header supports zero-initializing.
    #[inline]
    pub fn new() -> Self {
        Cable {
            mem: NonNull::new(unsafe { std::alloc::alloc_zeroed(Self::BASE_LAYOUT) as *mut H })
                .expect("allocation failed"),
            phantom: PhantomData,
        }
    }

    /// Constructs a new, empty `Cable<T, H>` on the heap with the given `header`.
    /// The block will always allocate on the heap.
    ///
    /// Prefer `with_capacity`.
    #[inline]
    pub fn with_header(value: H) -> Self {
        let mut block = Cable {
            mem: NonNull::new(unsafe { std::alloc::alloc_zeroed(Self::BASE_LAYOUT) as *mut H })
                .expect("allocation failed"),
            phantom: PhantomData,
        };
        block.set_header(value);
        return block;
    }

    /// Constructs a new, empty `Cable<T, H>` on the heap with the specified `capacity` and `header`.
    /// The block will be able to hold exactly `capacity` elements without reallocation.
    ///
    /// If `capacity` is 0 or `T` is zero-sized the block will still allocate.
    #[inline]
    pub fn with_capacity(capacity: usize, header: H) -> Self {
        let mut block = Cable {
            mem: {
                let layout = Self::BASE_LAYOUT
                    .extend(Layout::array::<T>(capacity).unwrap())
                    .unwrap()
                    .0;
                NonNull::new(unsafe { std::alloc::alloc(layout) as *mut H })
                    .expect("allocation failed")
            },
            phantom: PhantomData,
        };
        block.set_header(header);
        block.set_cap(capacity);
        return block;
    }

    /// Constructs a new, empty `Cable<T, H>` on the heap with the specified `capacity` and `header`.
    /// The block will be able to hold exactly `capacity` elements without reallocation.
    ///
    /// If `capacity` is 0 or `T` is zero-sized the block will still allocate. Fills the storage with `0` bytes
    #[inline]
    pub fn with_capacity_zeroed(capacity: usize, header: H) -> Self {
        let mut block = Cable {
            mem: {
                let layout = Self::BASE_LAYOUT
                    .extend(Layout::array::<T>(capacity).unwrap())
                    .unwrap()
                    .0;
                NonNull::new(unsafe { std::alloc::alloc_zeroed(layout) as *mut H })
                    .expect("allocation failed")
            },
            phantom: PhantomData,
        };
        block.set_header(header);
        block.set_cap(capacity);
        return block;
    }

    pub fn from_slice(slice: &[T]) -> Self {
        let mut block = Cable {
            mem: {
                let layout = Self::BASE_LAYOUT
                    .extend(Layout::array::<T>(slice.len()).unwrap())
                    .unwrap()
                    .0;
                NonNull::new(unsafe { std::alloc::alloc(layout) as *mut H })
                    .expect("allocation failed")
            },
            phantom: PhantomData,
        };
        unsafe { ptr::copy_nonoverlapping(slice.as_ptr(), block.as_mut_ptr(), slice.len()) }
        block.set_cap(slice.len());
        return block;
    }

    /// Constructs a new, empty `Cable<T, H>` on the heap with the specified capacity.
    /// Then fills it with `capacity` elements from `ptr` and sets the header to `header`.
    /// The block will be able to hold exactly capacity elements without reallocating.
    ///
    /// If capacity is 0 or `T` is zero-sized the block will still allocate. Fills the storage with `0` bytes
    #[inline]
    pub unsafe fn from_raw_parts(header: H, capacity: usize, ptr: *mut T) -> Self {
        let mut block = Cable {
            mem: {
                let layout = Self::BASE_LAYOUT
                    .extend(Layout::array::<T>(capacity).unwrap())
                    .unwrap()
                    .0;
                NonNull::new(std::alloc::alloc(layout) as *mut H).expect("allocation failed")
            },
            phantom: PhantomData,
        };
        ptr::copy_nonoverlapping(ptr, block.as_mut_ptr(), capacity);
        block.set_cap(capacity);
        block.set_header(header);
        return block;
    }

    /// Returns `true` if the block contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.cap() == 0
    }

    /// Fills the storage with `0` bytes. Does not impact header or size
    #[inline]
    pub fn zero(&mut self) {
        // SAFE(within bounds)
        unsafe {
            self.as_mut_ptr()
                .write_bytes(0, mem::size_of::<T>() * self.cap());
        }
    }

    #[inline]
    pub unsafe fn into_raw_parts(&self) -> (Option<&H>, usize, NonNull<T>) {
        let me = mem::ManuallyDrop::new(self);
        (me.header(), me.cap(), me.payload())
    }

    /// Converts the block into a `Box<H>`.
    ///
    /// # Safety
    /// Does not guarantee that returned header is initialized
    #[inline]
    pub fn into_boxed_header(self) -> Option<Box<H>> {
        if Self::HEADER_EXISTS {
            unsafe {
                let layout = Self::BASE_LAYOUT
                    .extend(Layout::array::<T>(self.cap()).ok()?)
                    .ok()?
                    .0;
                let new_ptr =
                    std::alloc::realloc(self.mem.as_ptr().cast(), layout, mem::size_of::<H>());
                Some(Box::from_raw(new_ptr.cast()))
            }
        } else {
            None
        }
    }

    /// Converts the block into a `Box<[T]>`.
    ///
    /// # Safety
    /// Does not guarantee that returned slice is initialized
    #[inline]
    pub fn into_boxed_slice(self) -> Option<Box<[T]>> {
        let capacity = self.cap(); // store the capacity because we deallocate the memory that holds it
        if capacity != 0 {
            unsafe {
                let old_layout = Self::BASE_LAYOUT
                    .extend(Layout::array::<T>(capacity).ok()?)
                    .ok()?
                    .0;
                let new_layout = Layout::array::<T>(capacity).ok()?;
                let me = mem::ManuallyDrop::new(self);
                let new_ptr = std::alloc::alloc(new_layout);
                ptr::copy_nonoverlapping(me.as_mut_ptr(), new_ptr.cast(), capacity);
                std::alloc::dealloc(me.mem.as_ptr().cast(), old_layout);
                let slice = slice::from_raw_parts_mut(new_ptr.cast(), capacity);
                Some(Box::from_raw(slice))
            }
        } else {
            None
        }
    }

    #[inline]
    fn current_memory(&self) -> Option<(NonNull<H>, Layout)> {
        if self.cap() == 0 {
            None
        } else {
            Some((
                self.mem,
                Self::BASE_LAYOUT
                    .extend(Layout::array::<T>(self.cap()).ok()?)
                    .ok()?
                    .0,
            ))
        }
    }

    /// Reserves the capacity for exactly additional more elements to be inserted in the given `Cable<H, T>`.
    /// After calling `reserve`, capacity will be equal to `self.cap() + additional`.
    ///
    /// Returns the new layout of the block or `None` if an error occured.
    pub fn reserve(&mut self, additional: usize, zeroed: bool) -> Option<Layout> {
        if additional > 0 {
            if let Some((ptr, old_layout)) = self.current_memory() {
                let (new_layout, old_size) = old_layout
                    .extend(Layout::array::<T>(additional).ok()?)
                    .ok()?;
                unsafe {
                    let new_size = new_layout.size();
                    let raw_ptr = std::alloc::realloc(ptr.as_ptr().cast(), new_layout, new_size);
                    self.mem = NonNull::new(raw_ptr as *mut H)?;
                    self.inc_cap(additional);
                    if zeroed {
                        raw_ptr.add(old_size).write_bytes(0, new_size - old_size)
                    }
                }
                Some(new_layout)
            } else {
                let new_layout = Layout::array::<T>(additional).ok()?;
                unsafe {
                    let new_ptr = if zeroed {
                        std::alloc::alloc_zeroed(new_layout)
                    } else {
                        std::alloc::alloc(new_layout)
                    };
                    self.mem = NonNull::new(new_ptr as *mut H)?;
                    self.set_cap(additional);
                }
                Some(new_layout)
            }
        } else {
            None
        }
    }

    /// Shrinks the block, keeping only `capacity` elements and deallocating the rest.
    /// After calling `truncate`, capacity will be equal to `capacity`.
    ///
    /// Returns the new layout of the block or `None` if an error occured.
    pub fn truncate(&mut self, capacity: usize) -> Option<Layout> {
        if capacity > self.cap() {
            return None;
        }

        if let Some((ptr, old_layout)) = self.current_memory() {
            unsafe {
                let raw_ptr = std::alloc::realloc(
                    ptr.as_ptr().cast(),
                    old_layout,
                    Self::BASE_LAYOUT.size() + capacity * mem::size_of::<T>(),
                );
                self.mem = NonNull::new(raw_ptr as *mut H)?;
                self.set_cap(capacity);
            }
        }

        let removed = Layout::array::<T>(self.cap() - capacity).ok()?;
        Some(Self::BASE_LAYOUT.extend(removed).ok()?.0)
    }

    /// Shrinks or grows the block, ensuring exactly `capacity` elements,
    /// and allocating / deallocating the rest.
    ///
    /// After calling `resize`, capacity will be equal to `new_cap`.
    ///
    /// Returns the new layout of the block or `None` if an error occured.
    #[inline]
    pub fn resize(&mut self, new_cap: usize) -> Option<Layout> {
        if new_cap > self.cap() {
            self.reserve(new_cap - self.cap(), false)
        } else {
            self.truncate(new_cap)
        }
    }

    /// Get a reference to the header or `None` if header does not exist.
    #[inline]
    pub fn header(&self) -> Option<&H> {
        if Self::HEADER_EXISTS {
            // SAFE(header must exist)
            Some(unsafe { &*self.mem.as_ptr() })
        } else {
            None
        }
    }

    /// Get a mutable reference to the header or `None` if header does not exist.
    #[inline]
    pub fn header_mut(&mut self) -> Option<&mut H> {
        if Self::HEADER_EXISTS {
            // SAFE(header must exist)
            Some(unsafe { &mut *self.mem.as_ptr() })
        } else {
            None
        }
    }

    /// If a header exists set it to `value`
    #[inline]
    pub fn set_header(&mut self, value: H) {
        if Self::HEADER_EXISTS {
            // SAFE(header must exist)
            unsafe { *self.mem.as_ptr() = value }
        }
    }

    /// Returns the number of `elements` the block can hold without reallocating.
    #[inline]
    pub fn cap(&self) -> usize {
        // SAFE(SIZE_OFFSET always valid)
        unsafe {
            let ptr = self.mem.as_ptr() as *mut u8;
            *(ptr.offset(Self::SIZE_OFFSET) as *mut usize)
        }
    }

    #[inline]
    fn set_cap(&mut self, capacity: usize) {
        // SAFE(SIZE_OFFSET always valid)
        unsafe {
            let ptr = self.mem.as_ptr() as *mut u8;
            *(ptr.offset(Self::SIZE_OFFSET) as *mut usize) = capacity;
        }
    }

    #[inline]
    fn inc_cap(&mut self, capacity: usize) {
        // SAFE(SIZE_OFFSET always valid)
        unsafe {
            let ptr = self.mem.as_ptr() as *mut u8;
            *(ptr.offset(Self::SIZE_OFFSET) as *mut usize) += capacity;
        }
    }

    /// Returns total `bytes` on heap.
    #[inline]
    pub fn footprint(&self) -> usize {
        mem::size_of::<H>()
            + Self::SIZE_PADDING
            + mem::size_of::<usize>()
            + Self::PAYLOAD_PADDING
            + (mem::size_of::<T>() * self.cap())
    }

    /// Gets a pointer to the `payload`.
    ///
    /// # Safety
    /// Pointer is guaranteed to be non-null but using can still lead to UB,
    #[inline]
    pub unsafe fn payload(&self) -> NonNull<T> {
        let ptr = self.mem.as_ptr() as *mut u8;
        NonNull::new(ptr.offset(Self::PAYLOAD_OFFSET) as *mut T).unwrap()
    }

    /// Gets a constant pointer to the payload.
    #[inline]
    pub unsafe fn as_ptr(&self) -> *const T {
        let ptr = self.mem.as_ptr() as *mut u8;
        ptr.offset(Self::PAYLOAD_OFFSET) as *const T
    }

    /// Gets a mutable pointer to the payload.
    #[inline]
    pub unsafe fn as_mut_ptr(&self) -> *mut T {
        let ptr = self.mem.as_ptr() as *mut u8;
        ptr.offset(Self::PAYLOAD_OFFSET) as *mut T
    }

    /// Extracts a slice containing all elements in the block.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self
    }

    /// Extracts a mutable slice containing all elements in the block.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self
    }

    #[inline]
    pub fn as_byte_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.as_ptr().cast(), self.cap() * mem::size_of::<T>()) }
    }
}

impl<T, H> ops::Deref for Cable<T, H> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] {
        // SAFE(within bounds)
        unsafe { slice::from_raw_parts(self.as_ptr(), self.cap()) }
    }
}

impl<T, H> ops::DerefMut for Cable<T, H> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        // SAFE(within bounds)
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.cap()) }
    }
}

impl<T, H, I: slice::SliceIndex<[T]>> ops::Index<I> for Cable<T, H> {
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        ops::Index::index(&**self, index)
    }
}

impl<T, H, I: slice::SliceIndex<[T]>> ops::IndexMut<I> for Cable<T, H> {
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        ops::IndexMut::index_mut(&mut **self, index)
    }
}

impl<T, H> Cable<T, H> {
    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.cap() {
            // SAFE(within bounds)
            Some(unsafe { &*self.as_ptr().add(index) })
        } else {
            None
        }
    }

    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index < self.cap() {
            // SAFE(within bounds)
            Some(unsafe { &mut *self.as_mut_ptr().add(index) })
        } else {
            None
        }
    }

    #[inline]
    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        &*self.as_ptr().add(index)
    }

    #[inline]
    pub unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
        &mut *self.as_mut_ptr().add(index)
    }
}

impl<T, H> Cable<T, H> {
    /// Insert `value` at `index` and return reference to that position if successful
    #[inline]
    pub fn set(&mut self, index: usize, value: T) -> Option<&mut T> {
        if index < self.cap() {
            // SAFE(within bounds)
            unsafe {
                let ptr = self.as_mut_ptr().add(index);
                *ptr = value;
                Some(&mut *ptr)
            }
        } else {
            None
        }
    }

    /// Inserts `value` at `index` and return reference to that position, skips checks
    #[inline]
    pub unsafe fn set_unchecked(&mut self, index: usize, value: T) -> &mut T {
        let ptr = self.as_mut_ptr().add(index);
        *ptr = value;
        &mut *ptr
    }
}
/*
impl<T, H> Drop for Cable<T, H> {
    fn drop(&mut self) {
        println!("Cable dropped!");
    }
}
*/
#[cfg(test)]
mod tests {
    #[test]
    fn truncate() {
        let mut x: crate::Cable<u64> = crate::Cable::with_capacity(9, ());
        x[0] = 5;
        x[1] = 8;
        x[2] = 7;
        x.truncate(3);

        println!("{:?}", x[0]);
    }

    #[test]
    fn reserve() {
        let mut x: crate::Cable<u64> = crate::Cable::with_capacity(3, ());
        x[0] = 5;
        x[1] = 8;
        x[2] = 7;
        x.reserve(3, false);
        x[4] = 1;

        println!("{:?}", x[4]);
    }

    #[test]
    fn resize() {
        let mut x: crate::Cable<u64> = crate::Cable::with_capacity(3, ());
        x[0] = 5;
        x[1] = 8;
        x[2] = 7;
        x.resize(5);
        x[4] = 1;

        println!("{:?}", x[4]);
    }

    #[test]
    fn into_boxed_slice() {
        let mut x: crate::Cable<u64> = crate::Cable::with_capacity(5, ());
        x[0] = 5;
        x[1] = 8;
        x[2] = 7;
        x[4] = 1;
        let slice = x.into_boxed_slice().unwrap();

        println!("{:?}", slice[1]);
    }
}
