符号执行过程：
```
//@ require true
//@ ensure l * l <= n < (l + 1) * (l + 1)
x = n;
//@ [generated] n == x && true
l = 0;
//@ [generated] 0 == l && (n == x && true)
r = n + 1;
//@ [generated] n + 1 == r && (0 == l && (n == x && true))
//@ inv l * l <= n < r * r && l + 1 <= r && x == n
while (l + 1 < r) do {
    //@ [generated] (l * l <= n < r * r && l + 1 <= r && x == n) && (l + 1 < r)
    mid = (l + r) / 2;
    //@ [generated] (l + r) / 2 == mid && ((l * l <= n < r * r && l + 1 <= r && x == n) && (l + 1 < r))
    if (x < mid * mid)
    then {
        //@ [generated] ((l + r) / 2 == mid && ((l * l <= n < r * r && l + 1 <= r && x == n) && (l + 1 < r))) && x < mid * mid
        r = mid
        //@ [generated] exists r'. mid == r && (((l + r') / 2 == mid && ((l * l <= n < r' * r' && l + 1 <= r' && x == n) && (l + 1 < r'))) && x < mid * mid)
    }
    else {
        //@ [generated] ((l + r) / 2 == mid && ((l * l <= n < r * r && l + 1 <= r && x == n) && (l + 1 < r))) && !x < mid * mid
        l = mid
        //@ [generated] exists l'. mid == l && (((l' + r) / 2 == mid && ((l' * l' <= n < r * r && l' + 1 <= r && x == n) && (l' + 1 < r))) && !x < mid * mid)
    }
    //@ [generated] (exists r'. mid == r && (((l + r') / 2 == mid && ((l * l <= n < r' * r' && l + 1 <= r' && x == n) && (l + 1 < r'))) && x < mid * mid)) || (exists l'. mid == l && (((l' + r) / 2 == mid && ((l' * l' <= n < r * r && l' + 1 <= r && x == n) && (l' + 1 < r))) && !x < mid * mid))
    //@ [target] (l * l <= n < r * r && l + 1 <= r && x == n)
}
//@ [generated] (l * l <= n < r * r && l + 1 <= r && x == n) && !(l + 1 < r)
```

验证条件：
```
n + 1 == r && (0 == l && (n == x && true)) |-- l * l <= n < r * r && l + 1 <= r && x == n

(exists r'. mid == r && (((l + r') / 2 == mid && ((l * l <= n < r' * r' && l + 1 <= r' && x == n) && (l + 1 < r'))) && x < mid * mid)) || (exists l'. mid == l && (((l' + r) / 2 == mid && ((l' * l' <= n < r * r && l' + 1 <= r && x == n) && (l' + 1 < r))) && !x < mid * mid)) |-- (l * l <= n < r * r && l + 1 <= r && x == n)

(l * l <= n < r * r && l + 1 <= r && x == n) && !(l + 1 < r) |-- l * l <= n < (l + 1) * (l + 1)
```