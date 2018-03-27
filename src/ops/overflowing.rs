macro_rules! overflowing_impl {
    ($trait_name: ident, $method: ident, $t: ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(&self, v: &$t) -> ($t, bool) {
                <$t>::$method(*self, *v)
            }
        }
    };
    ($trait_name: ident, $method: ident, $t: ty,None) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(&self) -> ($t, bool) {
                <$t>::$method(*self)
            }
        }
    };
    ($trait_name: ident, $method: ident, $t: ty, $rhs: ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(&self, v: $rhs) -> ($t, bool) {
                <$t>::$method(*self, v)
            }
        }
    };
}

/// Wrapping addition along with a boolean indicating an arithmetic overflow.
pub trait OverflowingAdd: Sized {
    /// Performs wrapping addition along with a boolean indicating an arithmetic overflow.
    fn overflowing_add(&self, v: &Self) -> (Self, bool);
}

overflowing_impl!(OverflowingAdd, overflowing_add, u8);
overflowing_impl!(OverflowingAdd, overflowing_add, u16);
overflowing_impl!(OverflowingAdd, overflowing_add, u32);
overflowing_impl!(OverflowingAdd, overflowing_add, u64);
overflowing_impl!(OverflowingAdd, overflowing_add, usize);

overflowing_impl!(OverflowingAdd, overflowing_add, i8);
overflowing_impl!(OverflowingAdd, overflowing_add, i16);
overflowing_impl!(OverflowingAdd, overflowing_add, i32);
overflowing_impl!(OverflowingAdd, overflowing_add, i64);
overflowing_impl!(OverflowingAdd, overflowing_add, isize);

/// Wrapping subtraction along with a boolean indicating an arithmetic overflow.
pub trait OverflowingSub: Sized {
    /// Performs wrapping subtraction along with a boolean indicating an arithmetic overflow.
    fn overflowing_sub(&self, v: &Self) -> (Self, bool);
}

overflowing_impl!(OverflowingSub, overflowing_sub, u8);
overflowing_impl!(OverflowingSub, overflowing_sub, u16);
overflowing_impl!(OverflowingSub, overflowing_sub, u32);
overflowing_impl!(OverflowingSub, overflowing_sub, u64);
overflowing_impl!(OverflowingSub, overflowing_sub, usize);

overflowing_impl!(OverflowingSub, overflowing_sub, i8);
overflowing_impl!(OverflowingSub, overflowing_sub, i16);
overflowing_impl!(OverflowingSub, overflowing_sub, i32);
overflowing_impl!(OverflowingSub, overflowing_sub, i64);
overflowing_impl!(OverflowingSub, overflowing_sub, isize);

/// Wrapping multiplication along with a boolean indicating an arithmetic overflow.
pub trait OverflowingMul: Sized {
    /// Performs wrapping multiplication along with a boolean indicating an arithmetic overflow.
    fn overflowing_mul(&self, v: &Self) -> (Self, bool);
}

overflowing_impl!(OverflowingMul, overflowing_mul, u8);
overflowing_impl!(OverflowingMul, overflowing_mul, u16);
overflowing_impl!(OverflowingMul, overflowing_mul, u32);
overflowing_impl!(OverflowingMul, overflowing_mul, u64);
overflowing_impl!(OverflowingMul, overflowing_mul, usize);

overflowing_impl!(OverflowingMul, overflowing_mul, i8);
overflowing_impl!(OverflowingMul, overflowing_mul, i16);
overflowing_impl!(OverflowingMul, overflowing_mul, i32);
overflowing_impl!(OverflowingMul, overflowing_mul, i64);
overflowing_impl!(OverflowingMul, overflowing_mul, isize);

/// Wrapping division along with a boolean indicating an arithmetic overflow.
pub trait OverflowingDiv: Sized {
    /// Performs wrapping division along with a boolean indicating an arithmetic overflow.
    fn overflowing_div(&self, v: &Self) -> (Self, bool);
}

overflowing_impl!(OverflowingDiv, overflowing_div, u8);
overflowing_impl!(OverflowingDiv, overflowing_div, u16);
overflowing_impl!(OverflowingDiv, overflowing_div, u32);
overflowing_impl!(OverflowingDiv, overflowing_div, u64);
overflowing_impl!(OverflowingDiv, overflowing_div, usize);

overflowing_impl!(OverflowingDiv, overflowing_div, i8);
overflowing_impl!(OverflowingDiv, overflowing_div, i16);
overflowing_impl!(OverflowingDiv, overflowing_div, i32);
overflowing_impl!(OverflowingDiv, overflowing_div, i64);
overflowing_impl!(OverflowingDiv, overflowing_div, isize);

/// Wrapping remainder along with a boolean indicating an arithmetic overflow.
pub trait OverflowingRem: Sized {
    /// Calculates the remainder in an overflowing fashion along with a boolean indicating an
    /// arithmetic overflow.
    fn overflowing_rem(&self, v: &Self) -> (Self, bool);
}

overflowing_impl!(OverflowingRem, overflowing_rem, u8);
overflowing_impl!(OverflowingRem, overflowing_rem, u16);
overflowing_impl!(OverflowingRem, overflowing_rem, u32);
overflowing_impl!(OverflowingRem, overflowing_rem, u64);
overflowing_impl!(OverflowingRem, overflowing_rem, usize);

overflowing_impl!(OverflowingRem, overflowing_rem, i8);
overflowing_impl!(OverflowingRem, overflowing_rem, i16);
overflowing_impl!(OverflowingRem, overflowing_rem, i32);
overflowing_impl!(OverflowingRem, overflowing_rem, i64);
overflowing_impl!(OverflowingRem, overflowing_rem, isize);

/// Wrapping negation along with a boolean indicating an arithmetic overflow.
pub trait OverflowingNeg: Sized {
    /// Performs negation in an overflowing fashion along with a boolean indicating an arithmetic
    /// overflow.
    fn overflowing_neg(&self) -> (Self, bool);
}

overflowing_impl!(OverflowingNeg, overflowing_neg, u8, None);
overflowing_impl!(OverflowingNeg, overflowing_neg, u16, None);
overflowing_impl!(OverflowingNeg, overflowing_neg, u32, None);
overflowing_impl!(OverflowingNeg, overflowing_neg, u64, None);
overflowing_impl!(OverflowingNeg, overflowing_neg, usize, None);

overflowing_impl!(OverflowingNeg, overflowing_neg, i8, None);
overflowing_impl!(OverflowingNeg, overflowing_neg, i16, None);
overflowing_impl!(OverflowingNeg, overflowing_neg, i32, None);
overflowing_impl!(OverflowingNeg, overflowing_neg, i64, None);
overflowing_impl!(OverflowingNeg, overflowing_neg, isize, None);

/// Left bit shift in an overflowing fashion along with a boolean indicating a too large shift.
pub trait OverflowingShl: Sized {
    /// Performs left bit shift in an overflowing fashion along with a boolean indicating the shift
    /// is too large.
    fn overflowing_shl(&self, v: u32) -> (Self, bool);
}

overflowing_impl!(OverflowingShl, overflowing_shl, u8, u32);
overflowing_impl!(OverflowingShl, overflowing_shl, u16, u32);
overflowing_impl!(OverflowingShl, overflowing_shl, u32, u32);
overflowing_impl!(OverflowingShl, overflowing_shl, u64, u32);
overflowing_impl!(OverflowingShl, overflowing_shl, usize, u32);

overflowing_impl!(OverflowingShl, overflowing_shl, i8, u32);
overflowing_impl!(OverflowingShl, overflowing_shl, i16, u32);
overflowing_impl!(OverflowingShl, overflowing_shl, i32, u32);
overflowing_impl!(OverflowingShl, overflowing_shl, i64, u32);
overflowing_impl!(OverflowingShl, overflowing_shl, isize, u32);

/// Right bit shift in an overflowing fashion along with a boolean indicating a too large shift.
pub trait OverflowingShr: Sized {
    /// Performs right bit shift in an overflowing fashion along with a boolean indicating the
    /// is too large.
    fn overflowing_shr(&self, v: u32) -> (Self, bool);
}

overflowing_impl!(OverflowingShr, overflowing_shr, u8, u32);
overflowing_impl!(OverflowingShr, overflowing_shr, u16, u32);
overflowing_impl!(OverflowingShr, overflowing_shr, u32, u32);
overflowing_impl!(OverflowingShr, overflowing_shr, u64, u32);
overflowing_impl!(OverflowingShr, overflowing_shr, usize, u32);

overflowing_impl!(OverflowingShr, overflowing_shr, i8, u32);
overflowing_impl!(OverflowingShr, overflowing_shr, i16, u32);
overflowing_impl!(OverflowingShr, overflowing_shr, i32, u32);
overflowing_impl!(OverflowingShr, overflowing_shr, i64, u32);
overflowing_impl!(OverflowingShr, overflowing_shr, isize, u32);

/// Absolute value in an overflowing fashion along with a boolean indicating an arithmetic overflow.
pub trait OverflowingAbs: Sized {
    /// Computes the absolute value in an overflowing fashion along with a boolean indicating an
    /// arithmetic overflow.
    fn overflowing_abs(&self) -> (Self, bool);
}

impl OverflowingAbs for u8 {
    #[inline]
    fn overflowing_abs(&self) -> (Self, bool) {
        (*self, false)
    }
}

impl OverflowingAbs for u16 {
    #[inline]
    fn overflowing_abs(&self) -> (Self, bool) {
        (*self, false)
    }
}

impl OverflowingAbs for u32 {
    #[inline]
    fn overflowing_abs(&self) -> (Self, bool) {
        (*self, false)
    }
}

impl OverflowingAbs for u64 {
    #[inline]
    fn overflowing_abs(&self) -> (Self, bool) {
        (*self, false)
    }
}

impl OverflowingAbs for usize {
    #[inline]
    fn overflowing_abs(&self) -> (Self, bool) {
        (*self, false)
    }
}

overflowing_impl!(OverflowingAbs, overflowing_abs, i8, None);
overflowing_impl!(OverflowingAbs, overflowing_abs, i16, None);
overflowing_impl!(OverflowingAbs, overflowing_abs, i32, None);
overflowing_impl!(OverflowingAbs, overflowing_abs, i64, None);
overflowing_impl!(OverflowingAbs, overflowing_abs, isize, None);

// TODO: overflowing_pow in nightly?
// TODO: add tests
