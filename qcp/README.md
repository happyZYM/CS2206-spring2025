# 编译说明
请在本文件下新建一个无后缀名文件`CONFIGURE`，写入以下配置
```
COQBIN=[coq可执行文件所在的文件夹，coq 已经在 bin path 中可以留空]
SUF=[可执行文件后缀，windows下为.exe]
SL_DIR=[qcp-docker中SeparationLogic文件夹路径]
COMMON_STRATEGY_DIR=[qcp-docker中common文件夹路径]
```
请确保文件夹路径以`/`结尾，推荐使用绝对路径。

完成配置后在本文件下 `make` 即可。