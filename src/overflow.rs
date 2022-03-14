#[macro_export]
macro_rules! overflow_check {
    ($($c:tt)+) => {
        {
            // 'overflow' variable may be unused in release mode.
            #[allow(unused_variables)]
            let (result, overflow) = $($c)+;

            #[cfg(any(overflow_check, debug_assertions))]
            {
                if overflow {
                    panic!("extended arithmetic overflow")
                }
            }

            result
        }
    };
}

#[cfg(any(overflow_check, debug_assertions))]
pub const CHECKING_OVERFLOW: bool = true;

#[cfg(not(any(overflow_check, debug_assertions)))]
pub const CHECKING_OVERFLOW: bool = false;
