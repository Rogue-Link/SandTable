#include <iostream>
#include <vector>
#include <string>
#include <cstring>

// 定义消息头结构体
struct ResponseHeader {
    int32_t correlation_id;
};

// 从二进制数据转换为ResponseHeader结构体的函数声明
ResponseHeader convertBinaryToStruct(const std::vector<uint8_t>& binaryData);
