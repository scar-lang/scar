## Scar

General purpose systems programming language with a high-level, ruby-like syntax. Aims to achieve low-level control while still being readable and concise.

#### Example

```scar
type Pair[T, U]
	first T
	second U
end

def make_pair[T, U](first T, second U) Pair[T, U]
	return Pair[T, U](first: first, second: second)
end

def swap[T, U](pair Pair[T, U]) Pair[U, T]
	return Pair[U, T](first: pair.second, second: pair.first)
end

def add[T: i32|i64|f32|f64](a T, b T) T
	return a + b
end

pub def main() void
	val pair = swap[i32, ref(u8)](make_pair[i32, ref(u8)](42, "scar"))
	@print("{d} {s}\n", {add[i32](pair.second, 8)}, {pair.first})
end
```

#### Resources

- [Documentation](https://scarlang-docs.pages.dev)
- [VSCode Extension](https://marketplace.visualstudio.com/items?itemName=NavidM.scar)

---

<font color="grey">(Under construction)</font>
