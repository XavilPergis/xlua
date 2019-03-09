-- stat := ";"
-- 	     | "break"
-- 	     | "goto" :name
-- 	     | "do" <block> "end"
-- 	     | "while" <exp> "do" <block> "end"
-- 	     | "repeat" <block> "until" <exp>
-- 	     | "function" <funcname> <funcbody>
-- 	     | "local" "function" :name <funcbody>
-- 	     | "local" <namelist> ("=" explist)?
-- 	     | <label>
-- 	     | <if_stmt>
-- 	     | <for_stmt>
-- 	     | <varlist> "=" <explist>
-- 	     | <functioncall> ;;

do
    goto block
    local a = 1

    ::block::
    local a, b = 1, 2
    return foo
end

foo(1, 2)
foo {a = 2, b = 3, [f(x)] = "lol", {1, 2, 3}}
require "foo"
thing [[a bc d efg]]
thing [====[a bc d efg]====]

if 123 then
    print("123")
end

if 123 then
    print("123")
elseif a == b then
    print("a == b")
end

if 123 then
    print("123")
elseif a == b then
    print("a == b")
else
    print("other")
end

for x = a, b do
    print(x)
    print(x * 2)
end

for x = a, b, 2 do
    print(x)
    print(x * 2)
end

for a, b in foo(), bar()[w]() do
    print(a)
    print(b .. "foo")
end

a = 100
while a > 0 do
    print(a)
    a = a - 1
end

b = 10000
repeat
    print(b)
    b = b / 10
until b < 1

function foo()
    return "foo"
end

tab = {item = "thing"}

function tab.foo(x)
    print(x .. "/" .. x)
end

function tab:foo(x)
    print(self.item .. "/" .. x)
end

local function lol(x, y)
    return function()
        print(x + y)
    end
end

function a(x, ...)
    return x, ...
end
