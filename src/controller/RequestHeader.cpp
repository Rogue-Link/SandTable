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

// 从二进制数据转换为RequestHeader结构体的函数
RequestHeader convertBinaryToStruct(const std::vector<uint8_t>& binaryData) {
    RequestHeader header;
    size_t offset = 0;

    // 读取api_key
    std::memcpy(&header.api_key, &binaryData[offset], sizeof(header.api_key));
    offset += sizeof(header.api_key);

    // 读取api_version
    std::memcpy(&header.api_version, &binaryData[offset], sizeof(header.api_version));
    offset += sizeof(header.api_version);

    // 读取correlation_id
    std::memcpy(&header.correlation_id, &binaryData[offset], sizeof(header.correlation_id));
    offset += sizeof(header.correlation_id);

    // 读取client_id长度
    int16_t client_id_length;
    std::memcpy(&client_id_length, &binaryData[offset], sizeof(client_id_length));
    offset += sizeof(client_id_length);

    // 读取client_id
    if (client_id_length > 0) {
        header.client_id = std::string(reinterpret_cast<const char*>(&binaryData[offset]), client_id_length);
    } else {
        header.client_id = "";
    }

    return header;
}
