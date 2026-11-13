#[derive(Clone, Default)]
pub struct Record {
    pub value: u8,
}

pub struct Tuple(pub u8);

pub enum Choice {
    Empty,
    Value(u8),
}

pub const CONSTANT: u8 = 4;
pub static STATIC: u8 = 5;

pub const fn const_callable() -> u8 {
    6
}

macro_rules! generated {
    () => {
        pub fn expanded() -> u8 {
            3
        }
    };
}
generated!();

#[cfg(any())]
pub fn disabled() {}

#[cfg(test)]
pub fn test_only() {}

pub trait Abstract {
    fn declaration(&self) -> u8;
}

impl Abstract for Record {
    fn declaration(&self) -> u8 {
        self.value
    }
}

pub fn direct_trait(value: &Record) -> u8 {
    value.declaration()
}

pub fn generic_trait<T: Abstract>(value: &T) -> u8 {
    value.declaration()
}

pub fn outer() -> u8 {
    fn nested() -> u8 {
        5
    }
    nested()
}

pub fn indirect(callback: fn() -> u8) -> u8 {
    callback()
}

pub fn dynamic(value: &dyn Abstract) -> u8 {
    value.declaration()
}

pub fn with_closure(value: u8) -> u8 {
    let callback = || value + 1;
    callback()
}

pub fn with_drop(value: Vec<u8>) -> usize {
    value.len()
}
