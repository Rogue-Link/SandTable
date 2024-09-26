
#include <iostream>
#include <vector>
#include <string>
#include <cstring>

// 定义消息头结构体
struct RequestHeader {
    int16_t api_key;
    int16_t api_version;
    int32_t correlation_id;
    std::string client_id;
};

// 从二进制数据转换为RequestHeader结构体
RequestHeader convertBinaryToStruct(const std::vector<uint8_t>& binaryData);