extern "C"{
    #include "myMap.h"
    #include <string.h>
}
#include <iostream>
#include <map>
#include <string>

std::map<int, std::string> *myMap;

static void init_map(){
    if (myMap == nullptr){
        myMap = new std::map<int, std::string>();
    }
}

void map_insert(int key, const char *val){
    init_map();
    std::string myString(val);
    myMap->insert(std::make_pair(key, myString));
}

void map_delete(int key){
    init_map();
    myMap->erase(key);
}

char* map_search(int key){
    init_map();
    auto it = myMap->find(key);
    if(it != myMap->end()){
        std::string ret = it->second;
        return strdup(ret.c_str());
    } else {
        std::string ret = "find nothing";
        return strdup(ret.c_str());
    }
}