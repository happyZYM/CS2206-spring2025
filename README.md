# README

这是我们课程相关文件的repo。

其中包括了两个子模块SetsClass和compcert_lib



获取本repo内容指令：

```
git clone https://github.com/Arcadia-Y/CS2206-spring2025.git
git submodule init
git submodule update
```

或者使用

```
git clone git@github.com:Arcadia-Y/CS2206-spring2025.git
git submodule update --init --recursive
```


## 编译
repo和子模块内提供了相关的Makefile和_CoqProject用于整个项目文件的编译。

windows需要自行提供CONFIGURE文件用于提供相关依赖的地址，请在cs2206-spring2024目录下新建一个无后缀名文件CONFIGURE，然后将coq安装的路径写入该文件中。我们使用的coq版本为8.15.2

以cygwin编译环境下的CONFIGURE设置为例：

```
COQBIN=/cygdrive/d/Coq-8.15/bin/
SUF=   // 这里写SUF=.exe也可以
```



如果你的编译环境是windows的powershell, CONFIGURE设置为

```
COQBIN=D:\Coq-8.15\bin\\
SUF=.exe
```



如果你的编译环境是wsl，CONFIGURE设置为

```
COQBIN=/mnt/d/Coq-8.15/bin/
SUF=.exe
```



编译之前请先确认你的环境中是否有make，具体指令为:

```
make --version
```

如果没有，可以使用mingw32-make或者mingw64-make替代，当然也要确认环境中存在

```
mingw32-make --version
或是
mingw64-make --version
```





正式编译之前请先计算依赖，具体指令为：（这里如果你使用其它make，请做对应替换）

```
make depend
```

然后可以开始编译，具体指令为：

```
make
```

如果你希望他并发加速，那么可以使用make -j4，其中数字可以自由调整，具体取决于你的电脑有多少个核

## 关于 _CoqProject
请参照 `qcp/README.md` 中的内容，将 `_CoqProject` 文件中的 `($SL_DIR)` 和 `($COMMON_STRATEGY_DIR)` 替换成对应文件夹路径。

请注意，`_CoqProject` 中 physical path 不能以 `/` 结尾，例如 `-R qcp/sll SimpleC.EE` 不能写为 `-R qcp/sll/ SimpleC.EE`，否则会出现问题。
