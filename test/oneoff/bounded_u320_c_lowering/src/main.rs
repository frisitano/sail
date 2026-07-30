use libloading::{Library, Symbol};
use ruint::aliases::U320;
use std::env;

#[repr(C)]
#[derive(Clone, Copy, Debug)]
struct SailU320 {
    limbs: [u64; 5],
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
struct SailU256 {
    limbs: [u64; 4],
}

impl From<U320> for SailU320 {
    fn from(value: U320) -> Self {
        Self {
            limbs: value.into_limbs(),
        }
    }
}

impl From<SailU320> for U320 {
    fn from(value: SailU320) -> Self {
        Self::from_limbs(value.limbs)
    }
}

fn oracle(value: SailU320) -> U320 {
    value.into()
}

impl From<U320> for SailU256 {
    fn from(value: U320) -> Self {
        let limbs = value.into_limbs();
        Self {
            limbs: [limbs[0], limbs[1], limbs[2], limbs[3]],
        }
    }
}

type BinaryU320 = unsafe extern "C" fn(SailU320, SailU320) -> SailU320;
type BinaryU256 = unsafe extern "C" fn(SailU256, SailU256) -> SailU320;
type BinaryU320U64 = unsafe extern "C" fn(SailU320, u64) -> SailU320;
type BinaryU256U64 = unsafe extern "C" fn(SailU256, u64) -> SailU320;
type ModU320U64 = unsafe extern "C" fn(SailU320, u64) -> u64;
type CompareU320 = unsafe extern "C" fn(SailU320, SailU320) -> bool;
type CompareU320U64 = unsafe extern "C" fn(SailU320, u64) -> bool;

struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut value = self.0;
        value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        value ^ (value >> 31)
    }

    fn u319(&mut self) -> U320 {
        U320::from_limbs([
            self.next(),
            self.next(),
            self.next(),
            self.next(),
            self.next() & 0x7fff_ffff_ffff_ffff,
        ])
    }

    fn u255(&mut self) -> U320 {
        U320::from_limbs([
            self.next(),
            self.next(),
            self.next(),
            self.next() & 0x7fff_ffff_ffff_ffff,
            0,
        ])
    }

    fn u160(&mut self) -> U320 {
        U320::from_limbs([self.next(), self.next(), self.next() & 0xffff_ffff, 0, 0])
    }
}

fn edge_values() -> Vec<U320> {
    let mut values = vec![U320::ZERO, U320::ONE, U320::from(u64::MAX)];
    for bit in [63, 64, 127, 128, 159, 160, 191, 192, 255, 256, 318] {
        let value = U320::ONE << bit;
        values.push(value);
        values.push(value - U320::ONE);
    }
    values.push((U320::ONE << 319) - U320::ONE);
    values
}

fn main() {
    let model_path = env::var_os("MODEL_LIB").expect("MODEL_LIB is required");
    // SAFETY: The generated model library and symbols are built immediately
    // before this process from model.sail, and SailU320 mirrors the generated
    // five-u64 C value carrier.
    unsafe {
        let library = Library::new(model_path).expect("load generated model");
        let add: Symbol<BinaryU320> = library.get(b"zadd_u320\0").unwrap();
        let sub: Symbol<BinaryU320> = library.get(b"zsub_u320\0").unwrap();
        let mul: Symbol<BinaryU256> = library.get(b"zmul_u320\0").unwrap();
        let add_u64: Symbol<BinaryU320U64> = library.get(b"zadd_u320_u64\0").unwrap();
        let sub_u64: Symbol<BinaryU320U64> = library.get(b"zsub_u320_u64\0").unwrap();
        let mul_u64: Symbol<BinaryU256U64> = library.get(b"zmul_u320_u64\0").unwrap();
        let div_u64: Symbol<BinaryU320U64> = library.get(b"zdiv_u320_u64\0").unwrap();
        let rem_u64: Symbol<ModU320U64> = library.get(b"zmod_u320_u64\0").unwrap();
        let div: Symbol<BinaryU320> = library.get(b"zdiv_u320\0").unwrap();
        let rem: Symbol<BinaryU320> = library.get(b"zmod_u320\0").unwrap();
        let lt: Symbol<CompareU320> = library.get(b"zlt_u320\0").unwrap();
        let lteq: Symbol<CompareU320> = library.get(b"zlteq_u320\0").unwrap();
        let gt: Symbol<CompareU320> = library.get(b"zgt_u320\0").unwrap();
        let gteq: Symbol<CompareU320> = library.get(b"zgteq_u320\0").unwrap();
        let eq: Symbol<CompareU320> = library.get(b"zeq_u320\0").unwrap();
        let neq: Symbol<CompareU320> = library.get(b"zneq_u320\0").unwrap();
        let lt_u64: Symbol<CompareU320U64> = library.get(b"zlt_u320_u64\0").unwrap();
        let eq_u64: Symbol<CompareU320U64> = library.get(b"zeq_u320_u64\0").unwrap();

        let edges = edge_values();
        for &left in &edges {
            for &right in &edges {
                if left < (U320::ONE << 319) && right < (U320::ONE << 319) {
                    assert_eq!(oracle(add(left.into(), right.into())), left + right);
                    assert_eq!(
                        oracle(sub(left.into(), right.into())),
                        left.saturating_sub(right)
                    );
                    assert_eq!(lt(left.into(), right.into()), left < right);
                    assert_eq!(lteq(left.into(), right.into()), left <= right);
                    assert_eq!(gt(left.into(), right.into()), left > right);
                    assert_eq!(gteq(left.into(), right.into()), left >= right);
                    assert_eq!(eq(left.into(), right.into()), left == right);
                    assert_eq!(neq(left.into(), right.into()), left != right);
                    if !right.is_zero() {
                        assert_eq!(oracle(div(left.into(), right.into())), left / right);
                        assert_eq!(oracle(rem(left.into(), right.into())), left % right);
                    }
                }
            }
        }

        let scalar_edges = [1, 2, 3, u32::MAX as u64, 1 << 32, 1 << 63, u64::MAX];
        for &left in &edges {
            if left >= (U320::ONE << 319) {
                continue;
            }
            for &right in &scalar_edges {
                let wide_right = U320::from(right);
                assert_eq!(oracle(add_u64(left.into(), right)), left + wide_right);
                assert_eq!(
                    oracle(sub_u64(left.into(), right)),
                    left.saturating_sub(wide_right)
                );
                assert_eq!(oracle(div_u64(left.into(), right)), left / wide_right);
                assert_eq!(rem_u64(left.into(), right), (left % wide_right).as_limbs()[0]);
                assert_eq!(lt_u64(left.into(), right), left < wide_right);
                assert_eq!(eq_u64(left.into(), right), left == wide_right);
            }
        }

        let mut rng = SplitMix64(0xe5a1_0320_5a11_cafe);
        for _ in 0..20_000 {
            let left = rng.u319();
            let right = rng.u319();
            let left160 = rng.u160();
            let right160 = rng.u160();
            let left255 = rng.u255();
            let scalar = rng.next();
            let divisor = rng.next() | 1;
            let wide_scalar = U320::from(scalar);
            let wide_divisor = U320::from(divisor);

            assert_eq!(oracle(add(left.into(), right.into())), left + right);
            assert_eq!(
                oracle(sub(left.into(), right.into())),
                left.saturating_sub(right)
            );
            assert_eq!(
                oracle(mul(left160.into(), right160.into())),
                left160 * right160
            );
            assert_eq!(
                oracle(add_u64(left.into(), scalar)),
                left + wide_scalar
            );
            assert_eq!(
                oracle(sub_u64(left.into(), scalar)),
                left.saturating_sub(wide_scalar)
            );
            assert_eq!(
                oracle(mul_u64(left255.into(), scalar)),
                left255 * wide_scalar
            );
            assert_eq!(
                oracle(div_u64(left.into(), divisor)),
                left / wide_divisor
            );
            assert_eq!(
                rem_u64(left.into(), divisor),
                (left % wide_divisor).as_limbs()[0]
            );
            let nonzero_right = if right.is_zero() { U320::ONE } else { right };
            assert_eq!(
                oracle(div(left.into(), nonzero_right.into())),
                left / nonzero_right
            );
            assert_eq!(
                oracle(rem(left.into(), nonzero_right.into())),
                left % nonzero_right
            );
            assert_eq!(lt(left.into(), right.into()), left < right);
            assert_eq!(lteq(left.into(), right.into()), left <= right);
            assert_eq!(gt(left.into(), right.into()), left > right);
            assert_eq!(gteq(left.into(), right.into()), left >= right);
            assert_eq!(eq(left.into(), right.into()), left == right);
            assert_eq!(neq(left.into(), right.into()), left != right);
            assert_eq!(lt_u64(left.into(), scalar), left < wide_scalar);
            assert_eq!(eq_u64(left.into(), scalar), left == wide_scalar);
        }
    }
}
