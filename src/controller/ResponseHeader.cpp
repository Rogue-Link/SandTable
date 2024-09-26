#include <iostream>
#include <vector>
#include <string>
#include <cstring>

// 定义消息头结构体
struct ResponseHeader {
    int32_t correlation_id;
};

// 从二进制数据转换为ResponseHeader结构体的函数
ResponseHeader convertBinaryToStruct(const std::vector<uint8_t>& binaryData) {
    ResponseHeader header;
    size_t offset = 0;

    // 读取correlation_id
    std::memcpy(&header.correlation_id, &binaryData[offset], sizeof(header.correlation_id));
    offset += sizeof(header.correlation_id);

    return header;
}