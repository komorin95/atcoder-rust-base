// -*- coding:utf-8-unix -*-

use proconio::{input, fastout};

#[fastout]
fn main() {
    input! {
        n: usize,
        mut plan: [(i32, i32, i32); n],  // Vec<(i32, i32, i32)>
    }
}

use num_traits::{pow, One};
use std::ops::{Add, Div, Mul, Sub};

const MODULUS: usize = 1000000007;

#[derive(Clone, Copy, PartialEq, Debug)]
struct ModP(usize);

impl One for ModP {
    fn one() -> Self {
        return ModP(1);
    }
}
impl Add for ModP {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        return ModP((self.0 + rhs.0) % MODULUS);
    }
}
impl Sub for ModP {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        return ModP((self.0 + MODULUS - rhs.0) % MODULUS);
    }
}
impl Mul for ModP {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        return ModP((self.0 * rhs.0) % MODULUS);
    }
}
impl Div for ModP {
    type Output = Self;
    fn div(self, rhs: Self) -> Self {
        if rhs.0 == 0 {
            panic!("Tried to divide by ModP(0)!");
        }
        let rhs_inv = pow(rhs, MODULUS - 2);
        return self * rhs_inv;
    }
}

// BIT from https://github.com/rust-lang-ja/atcoder-rust-base/blob/ja-all-enabled/examples/abc157-e-proconio.rs
// It requires commutativity so that "plus" operation works
use alga::general::{AbstractGroupAbelian, Additive, Operator};
use std::marker::PhantomData;
use std::ops::{RangeInclusive, RangeTo, RangeToInclusive};

struct FenwickTree<A, O> {
    partial_sums: Vec<A>,
    phantom_operator: PhantomData<O>,
}

impl<A: AbstractGroupAbelian<O>, O: Operator> FenwickTree<A, O> {
    fn new(n: usize) -> Self {
        Self {
            partial_sums: vec![A::identity(); n],
            phantom_operator: PhantomData,
        }
    }

    fn operate_to_index(&mut self, i: usize, x: &A) {
        let mut i1 = i + 1;
        while i1 <= self.partial_sums.len() {
            self.partial_sums[i1 - 1] = self.partial_sums[i1 - 1].operate(x);
            // add "the last nonzero bit" to i1
            i1 += 1 << i1.trailing_zeros();
        }
    }
}

trait RangeQuery<T> {
    type Output;
    fn query(&self, r: T) -> Self::Output;
}

impl<A: AbstractGroupAbelian<O>, O: Operator> RangeQuery<RangeToInclusive<usize>>
    for FenwickTree<A, O>
{
    type Output = A;
    fn query(&self, range: RangeToInclusive<usize>) -> A {
        let mut sum = A::identity();
        let mut i1 = range.end + 1;
        while i1 > 0 {
            sum = sum.operate(&self.partial_sums[i1 - 1]);
            i1 -= 1 << i1.trailing_zeros();
        }
        return sum;
    }
}

impl<A: AbstractGroupAbelian<O>, O: Operator> RangeQuery<RangeTo<usize>>
    for FenwickTree<A, O>
{
    type Output = A;
    fn query(&self, range: RangeTo<usize>) -> A {
        if range.end == 0 {
            return A::identity();
        } else {
            return self.query(..=range.end - 1);
        }
    }
}

impl<A: AbstractGroupAbelian<O>, O: Operator> RangeQuery<RangeInclusive<usize>>
    for FenwickTree<A, O>
{
    type Output = A;
    fn query(&self, range: RangeInclusive<usize>) -> A {
        return self
            .query(..=*range.end())
            .operate(&self.query(..*range.start()).two_sided_inverse());
    }
}
