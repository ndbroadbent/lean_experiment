use verified_rust::{fibonacci, math, strings};

fn main() {
    println!("=== Verified Rust Examples ===\n");

    // Math examples
    println!("Math:");
    println!("  1 + 1 = {}", math::add(1, 1));
    println!("  gcd(48, 18) = {}", math::gcd(48, 18));
    println!("  is_prime(17) = {}", math::is_prime(17));
    println!("  factorial(10) = {:?}", math::factorial(10));
    println!();

    // Fibonacci examples
    println!("Fibonacci:");
    println!("  fib(10) = {}", fibonacci::fib_iter(10));
    println!("  fib(20) = {}", fibonacci::fib_iter(20));
    println!("  fib_sequence(10) = {:?}", fibonacci::fib_sequence(10));
    println!("  is_fibonacci(55) = {}", fibonacci::is_fibonacci(55));
    println!("  fib_matrix(50) = {}", fibonacci::fib_matrix(50));
    println!();

    // String examples
    println!("Strings:");
    println!("  concat(\"hello\", \" world\") = \"{}\"", strings::concat("hello", " world"));
    println!("  is_palindrome(\"racecar\") = {}", strings::is_palindrome("racecar"));
    println!("  validate_and_process(\"hello\") = {:?}", strings::validate_and_process("hello"));
    println!("  validate_and_process(\"hi\") = {:?}", strings::validate_and_process("hi"));
    println!("  validate_and_process(\"way too long\") = {:?}", strings::validate_and_process("way too long"));
}
