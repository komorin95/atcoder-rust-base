// -*- coding:utf-8-unix -*-

#[cfg(debug_assertions)]
#[allow(unused)]
macro_rules! debug_eprintln {
    ($p:tt, $($x:expr),*) => {
        eprintln!($p, $($x,)*);
    };
}

#[cfg(not(debug_assertions))]
#[allow(unused)]
macro_rules! debug_eprintln {
    ($p:tt, $($x:expr),*) => {};
}

use proconio::{fastout, input};

#[fastout]
fn main() {
    input! {
        n: usize,
        mut _plan: [(i32, i32, i32); n],  // Vec<(i32, i32, i32)>
    }
}

const MODULUS: usize = 1000000007;
// const MODULUS: usize = 998244353;

#[allow(unused)]
mod static_prime_modint {
    use crate::MODULUS;
    use num_traits::{pow, One};
    use std::ops::{Add, Div, Mul, Sub};

    #[derive(Clone, Copy, PartialEq, Debug)]
    pub struct ModP(usize);
    impl ModP {
        pub fn new(x: usize) -> Self {
            ModP(x % MODULUS)
        }
        pub fn value(&self) -> usize {
            self.0
        }
    }
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

    #[derive(Clone, Debug)]
    pub struct CombinatoricsTable {
        factorial_table: Vec<ModP>,
        stirling_second_table: Vec<Vec<ModP>>,
    }
    impl CombinatoricsTable {
        pub fn new(src_max: usize, dist_max: usize) -> Self {
            let mut factorial_table = vec![ModP(1)];
            for i in 1..=dist_max {
                factorial_table.push(ModP(i) * factorial_table[i - 1]);
            }
            let mut stirling_second_table: Vec<Vec<ModP>> = Vec::with_capacity(src_max + 1);
            for n in 0..=src_max {
                let mut st_temp = vec![ModP(0); dist_max + 1];
                for k in 0..=dist_max {
                    if n == 0 && k == 0 {
                        st_temp[k] = ModP(1);
                    } else if n == 0 || k == 0 {
                        st_temp[k] = ModP(0);
                    } else {
                        st_temp[k] = ModP(k) * stirling_second_table[n - 1][k]
                            + stirling_second_table[n - 1][k - 1];
                    }
                }
                stirling_second_table.push(st_temp);
            }
            CombinatoricsTable {
                factorial_table,
                stirling_second_table,
            }
        }
        pub fn factorial(&self, n: usize) -> ModP {
            if self.factorial_table.len() > n {
                return self.factorial_table[n];
            } else {
                panic!("factorial_table is not long enough");
            }
        }
        pub fn stirling_second(&self, n: usize, k: usize) -> ModP {
            if self.stirling_second_table.len() > n && self.stirling_second_table[n].len() > k {
                return self.stirling_second_table[n][k];
            } else {
                panic!("stirling_second_table is not large enough");
            }
        }
        pub fn tw_any(&self, src: usize, dist: usize) -> ModP {
            pow(ModP(dist), src)
        }
        pub fn tw_inj(&self, src: usize, dist: usize) -> ModP {
            if src > dist {
                ModP(0)
            } else {
                self.factorial(dist) / self.factorial(dist - src)
            }
        }
        pub fn tw_surj(&self, src: usize, dist: usize) -> ModP {
            if src < dist {
                ModP(0)
            } else {
                self.factorial(dist) * self.stirling_second(src, dist)
            }
        }
        pub fn tw_inj_srcsym(&self, src: usize, dist: usize) -> ModP {
            if src > dist {
                ModP(0)
            } else {
                self.factorial(dist) / self.factorial(src) / self.factorial(dist - src)
            }
        }
    }

    // Number-theoretic transformation
    // The length of f must be a power of 2
    // and zeta must be a primitive f.len()th root of unity
    // start and skip should be 0 and 1 respectively for the root invocation
    // The inverse can be calculated by doing the same
    // with the original zeta's inverse as zeta
    // and dividing by f.len()
    pub fn number_theoretic_transformation(
        f: &Vec<ModP>,
        start: usize,
        skip: usize,
        zeta: ModP,
    ) -> Vec<ModP> {
        let n = f.len() / skip;
        if n == 1 {
            return vec![f[start]];
        }
        let g0 = number_theoretic_transformation(f, start, skip * 2, zeta * zeta);
        let g1 = number_theoretic_transformation(f, start + skip, skip * 2, zeta * zeta);
        let mut pow_zeta = ModP(1);
        let mut g = Vec::new();
        for i in 0..n {
            g.push(g0[i % (n / 2)] + pow_zeta * g1[i % (n / 2)]);
            pow_zeta = pow_zeta * zeta;
        }
        return g;
    }

    // convolution function
    pub fn convolution(aa: &[ModP], bb: &[ModP]) -> Vec<ModP> {
        let mut a: Vec<ModP> = aa.iter().cloned().collect();
        let mut b: Vec<ModP> = bb.iter().cloned().collect();
        let mut nn = 1;
        let mut nn_index = 0;
        while nn < aa.len() + bb.len() - 1 {
            nn *= 2;
            nn_index += 1;
        }
        while a.len() < nn {
            a.push(ModP(0));
        }
        while b.len() < nn {
            b.push(ModP(0));
        }
        debug_assert_eq!(MODULUS, 998244353); // TODO: support other primes
        debug_assert!(nn_index <= 23);
        let mut zeta = ModP(15311432); // a primitive 2^23-th root of unity
        while nn_index < 23 {
            zeta = zeta * zeta;
            nn_index += 1;
        }
        // Now zeta is a primitive nn-th root of unity
        let ahat = number_theoretic_transformation(&a, 0, 1, zeta);
        let bhat = number_theoretic_transformation(&b, 0, 1, zeta);
        let mut chat = Vec::new();
        for i in 0..nn {
            chat.push(ahat[i] * bhat[i]);
        }
        let mut c = number_theoretic_transformation(&chat, 0, 1, ModP(1) / zeta);
        for ci in &mut c {
            *ci = *ci / ModP(nn);
        }
        // Now c is the convolution
        for i in aa.len() + bb.len() - 1..c.len() {
            debug_assert_eq!(c[i], ModP::new(0));
        }
        c.resize(aa.len() + bb.len() - 1, ModP::new(0));
        return c;
    }
}

#[allow(unused)]
mod dynamic_modint {
    use crate::gcd;
    use num_traits::{PrimInt, Unsigned};
    use std::ops::{Add, Mul, Sub};

    #[derive(Clone, Copy, PartialEq, Debug)]
    pub struct ModM<T>(T, T);

    impl<T> ModM<T>
    where
        T: PrimInt + Unsigned,
    {
        pub fn new(a: T, m: T) -> Self {
            ModM(a % m, m)
        }
    }
    pub fn pow_modm<T>(base: ModM<T>, index: usize) -> ModM<T>
    where
        T: PrimInt + Unsigned,
    {
        if index == 0 {
            return ModM(T::one(), base.1);
        } else {
            if index % 2 == 0 {
                let half = pow_modm(base, index / 2);
                return half * half;
            } else {
                let half = pow_modm(base, index / 2);
                return half * half * base;
            }
        }
    }
    impl<T> Add for ModM<T>
    where
        T: PrimInt + Unsigned,
    {
        type Output = Self;
        fn add(self, rhs: Self) -> Self {
            if self.1 != rhs.1 {
                panic!("Tried to add two number in different modulus");
            }
            return ModM((self.0 + rhs.0) % self.1, self.1);
        }
    }
    impl<T> Sub for ModM<T>
    where
        T: PrimInt + Unsigned,
    {
        type Output = Self;
        fn sub(self, rhs: Self) -> Self {
            if self.1 != rhs.1 {
                panic!("Tried to subtract two number in different modulus");
            }
            return ModM((self.0 + self.1 - rhs.0) % self.1, self.1);
        }
    }
    impl<T> Mul for ModM<T>
    where
        T: PrimInt + Unsigned,
    {
        type Output = Self;
        fn mul(self, rhs: Self) -> Self {
            if self.1 != rhs.1 {
                panic!("Tried to multiply two number in different modulus");
            }
            return ModM((self.0 * rhs.0) % self.1, self.1);
        }
    }

    // For a = aa mod m,
    // it computes (g mod m, b mod m),
    // that satisfies g = gcd(aa,m) and aa*b = g mod m
    fn inv_gcd<T>(am: ModM<T>) -> (ModM<T>, ModM<T>)
    where
        T: PrimInt + Unsigned + std::fmt::Debug,
    {
        let a = am.0;
        let m = am.1;
        if m % a == T::zero() {
            return (am, ModM(T::one(), m));
        }
        let q = m / a;
        let r = m % a;
        let (ga, xa) = inv_gcd(ModM(r, a));
        let g = ga.0;
        let gm = ModM(g, m);
        let x = xa.0;
        if r * x > g {
            let y = (r * x - g) / a;
            let z = (q * x + y) % m;
            let zm = ModM(T::zero(), m) - ModM(z, m);
            debug_assert_eq!(am * zm, gm);
            return (gm, zm);
        } else {
            let y = (g - r * x) / a;
            let zm = ModM(y, m) - ModM((q * x) % m, m);
            debug_assert_eq!(am * zm, gm);
            return (gm, zm);
        }
    }

    // Two-term Chinese remainder theorem function
    fn crt<T>(am: ModM<T>, bmm: ModM<T>) -> Option<ModM<T>>
    where
        T: PrimInt + Unsigned + std::fmt::Debug,
    {
        let a = am.0;
        let m = am.1;
        let b = bmm.0;
        let mm = bmm.1;
        if m == mm {
            if a == b {
                return Some(am);
            } else {
                return None;
            }
        } else if m > mm {
            return crt(bmm, am);
        } else {
            // m < mm
            let (dmm, xmm) = inv_gcd(ModM(m, mm));
            let d = dmm.0;
            debug_assert_eq!(d, gcd(m, mm));
            let x = xmm.0;
            if a % d != b % d {
                return None;
            }
            let mmm = m * mm / d;
            if a == b {
                return Some(ModM(a, mmm));
            } else if a < b {
                let y = (b - a) / d;
                let ans = ModM(a, mmm) + ModM(m * x, mmm) * ModM(y, mmm);
                debug_assert_eq!(ans.0 % m, a);
                debug_assert_eq!(ans.0 % mm, b);
                return Some(ans);
            } else {
                // a > b
                let y = (a - b) / d;
                let ans = ModM(a, mmm) - ModM(m * x, mmm) * ModM(y, mmm);
                debug_assert_eq!(ans.0 % m, a);
                debug_assert_eq!(ans.0 % mm, b);
                return Some(ans);
            }
        }
    }

    // Helper function for number-theoretic transformation
    // lists Proth primes of the form
    // p = k * 2^n + 1
    // in the form
    // n k p a.
    // a^k is a primitive 2^n-th root of unity in mod p.
    pub fn list_proth_primes(max: usize) {
        for n in 1..64 {
            let two_n = 1 << n;
            if two_n >= max {
                break;
            }
            for k0 in 1..=(two_n / 2) {
                let k = 2 * k0 - 1;
                let p = k * two_n + 1;
                if p > max {
                    break;
                }
                let alist = vec![2, 3, 5, 7, 11, 13, 17, 19];
                for a in alist {
                    if a >= p {
                        break;
                    }
                    let sym = pow_modm(ModM(a as u128, p as u128), (p - 1) / 2);
                    if sym.0 == (p - 1) as u128 {
                        println!("{} {} {} {}", n, k, p, a);
                        break;
                    }
                }
            }
        }
    }

    pub fn check_powers(a: usize, p: usize, n: usize) {
        let mut aa = ModM(a as u128, p as u128);
        for i in 0..n {
            println!("{} times: {}", i, aa.0);
            aa = aa * aa;
        }
    }
}

// Binary search for closures
// returns the value i where f(i) == true but f(i+1) == false
// if forall i f(i) == true, returns max_value
#[allow(dead_code)]
fn closure_binary_search<T>(f: T, min_value: usize, max_value: usize) -> usize
where
    T: Fn(usize) -> bool,
{
    if !f(min_value) {
        panic!("Check the condition for closure_binary_search()");
    }
    if f(max_value) {
        return max_value;
    }
    let mut min_value = min_value;
    let mut max_value = max_value;
    while min_value + 1 < max_value {
        let check_value = min_value + (max_value - min_value) / 2;
        if f(check_value) {
            min_value = check_value;
        } else {
            max_value = check_value;
        }
    }
    return min_value;
}

// Iterator of proper subsets
// Caution: it does NOT starts with the universal set itself!
struct SubsetIterator {
    universal_set: usize,
    last_set: usize,
}
#[allow(dead_code)]
impl SubsetIterator {
    fn new(universal_set: usize) -> Self {
        SubsetIterator {
            universal_set,
            last_set: universal_set,
        }
    }
}
impl Iterator for SubsetIterator {
    type Item = usize;
    fn next(&mut self) -> Option<Self::Item> {
        if self.last_set == 0 {
            return None;
        } else {
            self.last_set -= 1;
            self.last_set &= self.universal_set;
            return Some(self.last_set);
        }
    }
}

use std::cell::Cell;

#[derive(Debug, Clone)]
struct EquivalenceRelation {
    parent: Vec<Cell<usize>>,
    rank: Vec<Cell<usize>>,
}

#[allow(dead_code)]
impl EquivalenceRelation {
    fn new(n: usize) -> Self {
        let mut parent = Vec::with_capacity(n);
        for i in 0..n {
            parent.push(Cell::new(i));
        }
        let rank = vec![Cell::new(0); n];
        return Self { parent, rank };
    }

    fn make_equivalent(&mut self, a: usize, b: usize) {
        let volume = self.parent.len();
        if a >= volume || b >= volume {
            panic!(
                "Tried to make {} and {} equivalent but there are only {} elements",
                a, b, volume
            );
        }
        let aa = self.find(a);
        let bb = self.find(b);
        if aa == bb {
            return;
        }
        let aarank = self.rank[aa].get();
        let bbrank = self.rank[bb].get();
        if aarank > bbrank {
            self.parent[bb].set(aa);
        // self.rank[aa] = aarank.max(bbrank + 1);
        } else {
            self.parent[aa].set(bb);
            self.rank[bb].set(bbrank.max(aarank + 1));
        }
    }

    fn find(&self, a: usize) -> usize {
        let volume = self.parent.len();
        if a >= volume {
            panic!("Tried to find {} but there are only {} elements", a, volume);
        }
        let b = self.parent[a].get();
        if b == a {
            return a;
        } else {
            let c = self.find(b);
            self.parent[a].set(c);
            return c;
        }
    }

    fn are_equivalent(&self, a: usize, b: usize) -> bool {
        return self.find(a) == self.find(b);
    }
}

// Segment tree for range minimum query and alike problems
// The closures must fulfill the defining laws of monoids
// Indexing is 0-based
// The code is based on that in C++ in the 'ant book'
#[derive(Clone, PartialEq, Debug)]
struct SegmentTree<A, CUnit, CMult> {
    data: Vec<A>,
    monoid_unit_closure: CUnit,
    monoid_op_closure: CMult,
}

#[allow(dead_code)]
impl<A, CUnit, CMult> SegmentTree<A, CUnit, CMult>
where
    A: Copy,
    CUnit: Fn() -> A,
    CMult: Fn(A, A) -> A,
{
    fn new(n: usize, monoid_unit_closure: CUnit, monoid_op_closure: CMult) -> Self {
        let mut nn = 1;
        while nn < n {
            nn *= 2;
        }
        let this = Self {
            data: vec![monoid_unit_closure(); 2 * nn - 1],
            monoid_unit_closure,
            monoid_op_closure,
        };
        return this;
    }

    fn update(&mut self, k: usize, a: A) {
        let n = (self.data.len() + 1) / 2;
        let mut k = k + n - 1;
        self.data[k] = a;
        while k > 0 {
            k = (k - 1) / 2;
            self.data[k] = (self.monoid_op_closure)(self.data[k * 2 + 1], self.data[k * 2 + 2]);
        }
    }

    fn query_internal(&self, a: usize, b: usize, k: usize, l: usize, r: usize) -> A {
        if r <= a || b <= l {
            return (self.monoid_unit_closure)();
        }
        if a <= l && r <= b {
            return self.data[k];
        } else {
            let vl = self.query_internal(a, b, k * 2 + 1, l, (l + r) / 2);
            let vr = self.query_internal(a, b, k * 2 + 2, (l + r) / 2, r);
            return (self.monoid_op_closure)(vl, vr);
        }
    }
}

trait RangeQuery<T> {
    type Output;
    fn query(&self, r: T) -> Self::Output;
}

use std::ops::Range;

#[allow(dead_code)]
impl<A, CUnit, CMult> RangeQuery<Range<usize>> for SegmentTree<A, CUnit, CMult>
where
    A: Copy,
    CUnit: Fn() -> A,
    CMult: Fn(A, A) -> A,
{
    type Output = A;
    fn query(&self, range: Range<usize>) -> A {
        let n = (self.data.len() + 1) / 2;
        return self.query_internal(range.start, range.end, 0, 0, n);
    }
}

#[allow(dead_code)]
fn divisors(n: u64) -> Vec<u64> {
    let mut divisors = Vec::new();
    for d in 1..=n {
        if d * d > n {
            break;
        }
        if n % d != 0 {
            continue;
        }
        divisors.push(d);
        if n / d != d {
            divisors.push(n / d);
        }
    }
    return divisors;
}

use num_traits::PrimInt;
#[allow(dead_code)]
fn gcd<T>(a: T, b: T) -> T
where
    T: PrimInt,
{
    if a < b {
        return gcd(b, a);
    } else if b == T::zero() {
        return a;
    } else {
        return gcd(b, a % b);
    }
}

use num_traits::Unsigned;
// Sum of floor((ai+b)/m) for i = 0..=n-1
// based on the (new) editorial of practice2-c
#[allow(dead_code)]
fn floor_sum<T>(n: T, m: T, a: T, b: T) -> T
where
    T: PrimInt + Unsigned,
{
    if n == T::zero() {
        return T::zero();
    }
    if a >= m || b >= m {
        return floor_sum(n, m, a % m, b % m)
            + (b / m) * n
            + (a / m) * n * (n - T::one()) / (T::one() + T::one());
    }
    // a, b < m
    if a == T::zero() {
        return T::zero();
    }
    // 0<a<m, 0<=b<m
    let y = (a * n + b) / m;
    let z = (a * n + b) % m;
    // a*n+b = y*m+z
    return floor_sum(y, a, m, z);
}
