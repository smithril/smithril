pub fn binary2integer(s: String) -> u64 {
    let mut res: u64 = 0;
    let mut mask: u64 = 1;
    if s.chars().count() > 64 {
        panic!("Binary size greater than 64 bits are not supported")
    }
    for sym in s.chars().rev() {
        if sym == '1' {
            res += mask;
        }
        mask <<= 1;
        println!("{} alalala", mask);
    }
    res
}
