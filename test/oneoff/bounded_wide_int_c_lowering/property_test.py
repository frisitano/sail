import ctypes
import os
import random


MASK64 = (1 << 64) - 1
MASK128 = (1 << 128) - 1
MASK256 = (1 << 256) - 1


class U128(ctypes.Structure):
    _fields_ = [("limbs", ctypes.c_uint64 * 2)]


class U256(ctypes.Structure):
    _fields_ = [("limbs", ctypes.c_uint64 * 4)]


def u128(value):
    return U128((ctypes.c_uint64 * 2)(value & MASK64, (value >> 64) & MASK64))


def u256(value):
    limbs = [((value >> (64 * index)) & MASK64) for index in range(4)]
    return U256((ctypes.c_uint64 * 4)(*limbs))


def integer(value):
    return sum(int(limb) << (64 * index) for index, limb in enumerate(value.limbs))


lib = ctypes.CDLL(os.environ["MODEL_LIB"])
for name, arguments, result in [
    ("zadd_widen_128", [U128, U128], U256),
    ("zmul_widen_128", [U128, U128], U256),
    ("zadd_256_128", [U256, U128], U256),
    ("zmul_256_128", [U256, U128], U256),
    ("zsub_256_128", [U256, U128], U256),
    ("zdiv_256_128", [U256, U128], U256),
    ("zmod_256_128", [U256, U128], U128),
    ("zlt_256_128", [U256, U128], ctypes.c_bool),
    ("zeq_256_128", [U256, U128], ctypes.c_bool),
    ("zneq_128_256", [U128, U256], ctypes.c_bool),
    ("zlt_128_256", [U128, U256], ctypes.c_bool),
    ("zsub_128_256", [U128, U256], U128),
    ("zdiv_128_256", [U128, U256], U128),
    ("zmod_128_256", [U128, U256], U128),
]:
    function = getattr(lib, name)
    function.argtypes = arguments
    function.restype = result


edge128 = [0, 1, MASK64, 1 << 64, (1 << 64) + 1, MASK128 - 1, MASK128]
edge256 = [0, 1, MASK64, 1 << 64, 1 << 127, 1 << 128, 1 << 191, 1 << 255, MASK256]

for left in edge128:
    for right in edge128:
        assert integer(lib.zadd_widen_128(u128(left), u128(right))) == left + right
        assert integer(lib.zmul_widen_128(u128(left), u128(right))) == left * right

for left in edge256:
    for right in edge128:
        assert integer(lib.zadd_256_128(u256(left), u128(right))) == (left + right) & MASK256
        assert integer(lib.zmul_256_128(u256(left), u128(right))) == (left * right) & MASK256
        if left >= right:
            assert integer(lib.zsub_256_128(u256(left), u128(right))) == left - right
        if right:
            assert integer(lib.zdiv_256_128(u256(left), u128(right))) == left // right
            assert integer(lib.zmod_256_128(u256(left), u128(right))) == left % right
        assert bool(lib.zlt_256_128(u256(left), u128(right))) == (left < right)
        assert bool(lib.zeq_256_128(u256(left), u128(right))) == (left == right)
        assert bool(lib.zneq_128_256(u128(right), u256(left))) == (right != left)
        assert bool(lib.zlt_128_256(u128(right), u256(left))) == (right < left)
        assert integer(lib.zsub_128_256(u128(right), u256(left))) == max(right - left, 0)
        if left:
            assert integer(lib.zdiv_128_256(u128(right), u256(left))) == right // left
            assert integer(lib.zmod_128_256(u128(right), u256(left))) == right % left

rng = random.Random(0xE5A101280256)
for _ in range(10000):
    left128 = rng.getrandbits(128)
    right128 = rng.getrandbits(128)
    left256 = rng.getrandbits(256)
    divisor = rng.getrandbits(128) or 1
    divisor256 = rng.getrandbits(256) or 1
    assert integer(lib.zadd_widen_128(u128(left128), u128(right128))) == left128 + right128
    assert integer(lib.zmul_widen_128(u128(left128), u128(right128))) == left128 * right128
    assert integer(lib.zadd_256_128(u256(left256), u128(right128))) == (left256 + right128) & MASK256
    assert integer(lib.zmul_256_128(u256(left256), u128(right128))) == (left256 * right128) & MASK256
    if left256 >= right128:
        assert integer(lib.zsub_256_128(u256(left256), u128(right128))) == left256 - right128
    assert integer(lib.zdiv_256_128(u256(left256), u128(divisor))) == left256 // divisor
    assert integer(lib.zmod_256_128(u256(left256), u128(divisor))) == left256 % divisor
    assert bool(lib.zlt_256_128(u256(left256), u128(right128))) == (left256 < right128)
    assert bool(lib.zeq_256_128(u256(left256), u128(right128))) == (left256 == right128)
    assert bool(lib.zneq_128_256(u128(right128), u256(left256))) == (right128 != left256)
    assert bool(lib.zlt_128_256(u128(right128), u256(left256))) == (right128 < left256)
    assert integer(lib.zsub_128_256(u128(right128), u256(left256))) == max(right128 - left256, 0)
    assert integer(lib.zdiv_128_256(u128(right128), u256(divisor256))) == right128 // divisor256
    assert integer(lib.zmod_128_256(u128(right128), u256(divisor256))) == right128 % divisor256
