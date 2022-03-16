# Deft

Deft is a systems programming language designed for safety and efficiency. In its design it is very similar to other modern lower level languages like Rust or Go — and list Rust it makes use of ownership to achieve safety at compile-time; however, simplifying it drastically in comparison to Rust.

The following is a walkthrough of the language features starting from the basics.

1. Bindings
2. Type System
3. Functions
4. Control Flow
5. Structures
6. Enumerations
7. Module system

## Bindings (or variable declarations)

A binding associates a value with a name. Bindings in Deft look like the following:

```deft
pi := 3.14
name := "john"
```

The shown method of bindings creates an immutable binding, i.e. those variables cannot have new values assigned to them. To create a mutable binding use the `var` keyword:

```deft
var x = 45
print(x)
x = 32 // can now reassign to x
print(x)
```

Bindings by default will infer the type of the created variable based on the value. However, you can also explicitly specify the type which can be useful when you would like to disagree with inferred type (or in some cases where there is no inferred type).

```deft
// by default 45 would be inferred to be i32 so the type annotation is useful here
n u64 := 45

// the compiler requires explicit type annotation for an empty array binding
list [i32] := []
```

## Type System

Deft's type system begins at the primitives, these are built-in basic types to represent integral values. The full list is as follows:

- `i8`, `i16`, `i32`, `i64`
- `u8`, `u16`, `u32`, `u64`
- `f32`, `f64`
- `bool`

There are two kinds of user-created types in Deft, structures and enumerations — both of which will be discussed in further detail in later sections. However, excluding those we can now cover "compound" types, which is how we refer to built-in types that are constructed with either primitive or user-created types. Currently these are array and box types, which look like `[T]` and `~T` respectively where T is the primitive or user-created type.

## Functions

In Deft to declare a function you start with the `fun` keyword followed by the name of the function. Then annotate types for the return value and parameters in the function signature as follows:

```deft
fun add_i32(n1 i32, n2 i32) i32 {
    return n1 + n2
}

fun main() {
    print()
}
```
