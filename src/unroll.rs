#[macro_export]
macro_rules! unroll_iter {
    ($v:ident, $i:expr, $c:block) => {{
        #[allow(dead_code)]
        let $v = $i;
        $c
    }};
}

#[macro_export]
macro_rules! unroll {
    (for $v:ident in 0..$n:tt $c:block) => {
        $crate::unroll!($n, $v, $c);
    };

    (1, $v:ident, $c:block) => {
        $crate::unroll_iter!($v, 0, $c)
    };
    (2, $v:ident, $c:block) => {
        $crate::unroll!(1, $v, $c);
        $crate::unroll_iter!($v, 1, $c)
    };
    (3, $v:ident, $c:block) => {
        $crate::unroll!(2, $v, $c);
        $crate::unroll_iter!($v, 2, $c)
    };
    (4, $v:ident, $c:block) => {
        $crate::unroll!(3, $v, $c);
        $crate::unroll_iter!($v, 3, $c)
    };
}

#[macro_export]
macro_rules! collect_array {
    (1, |$v:ident| $c:block) => {
        [$crate::unroll_iter!($v, 0, $c)]
    };
    (2, |$v:ident| $c:block) => {
        [
            $crate::unroll_iter!($v, 0, $c),
            $crate::unroll_iter!($v, 1, $c),
        ]
    };
    (3, |$v:ident| $c:block) => {
        [
            $crate::unroll_iter!($v, 0, $c),
            $crate::unroll_iter!($v, 1, $c),
            $crate::unroll_iter!($v, 2, $c),
        ]
    };
    (4, |$v:ident| $c:block) => {
        [
            $crate::unroll_iter!($v, 0, $c),
            $crate::unroll_iter!($v, 1, $c),
            $crate::unroll_iter!($v, 2, $c),
            $crate::unroll_iter!($v, 3, $c),
        ]
    };
}
