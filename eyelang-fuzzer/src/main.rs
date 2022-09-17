use rand::prelude::*;

fn main() {
    let lines = std::env::args()
        .skip(1)
        .next()
        .map(|s| s.parse().expect("provide number of lines as first argument"))
        .unwrap_or(100usize);
    let mut remaining_lines = lines as i64 - 1;
    
    println!("main :: fn {{}}");

    while remaining_lines > 0 {
        remaining_lines -= generate_random() as i64;
    }
    eprintln!("Generated {} lines", lines as i64 - remaining_lines);
}

fn random_name() -> String {
    let mut r = rand::thread_rng();
    let len = r.gen_range(8..20);
    
    (0..len).map(|_| r.gen_range('a'..='z')).collect()
}

fn generate_random() -> usize {
    print!("{} :: ", random_name());
    let mut r = rand::thread_rng();
    match r.gen_range(0..3) {
        0 => {
            let a = random_name();
            let b = random_name();
            println!("fn({a} i32, {b} i64) -> i16: i16 {a} + i16 {b}\n");
            2
        }
        1 => {
            let a = random_name();
            let b = random_name();
            let size = r.gen_range(0..100000);
            println!("struct {{\n    {a} **i64,\n    {b} [u128;{size}]\n}}\n");
            5
        }
        2 => {
            let x1 = random_name();
            let x2 = random_name();
            let string1 = random_name();
            let string2 = random_name();
            println!("fn -> *i8 {{");
            println!("    {x1} := \"{string1}\"");
            println!("    {x2} := \"{string2}\"");
            println!("    ret if 1 < (2+2) {{");
            println!("        ret {x1}");
            println!("    }} else {x2}");
            println!("}}\n");
            8
        }
        _ => unreachable!("not in range of random call")
    }
}
