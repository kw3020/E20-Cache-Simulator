/*
CS-UY 2214
Adapted from Jeff Epstein
Starter code for E20 cache Simulator
simcache.cpp
*/

#include <cstddef>
#include <iostream>
#include <string>
#include <vector>
#include <fstream>
#include <limits>
#include <iomanip>
#include <list>
#include <algorithm>
#include <regex>
#include <cmath>

using namespace std;




/*
    Prints out the correctly-formatted configuration of a cache.

    @param cache_name The name of the cache. "L1" or "L2"

    @param size The total size of the cache, measured in memory cells.
        Excludes metadata

    @param assoc The associativity of the cache. One of [1,2,4,8,16]

    @param blocksize The blocksize of the cache. One of [1,2,4,8,16,32,64])

    @param num_rows The number of rows in the given cache.
*/
void print_cache_config(const string &cache_name, int size, int assoc, int blocksize, int num_rows) {
    cout << "Cache " << cache_name << " has size " << size <<
        ", associativity " << assoc << ", blocksize " << blocksize <<
        ", rows " << num_rows << endl;
}

/*
    Prints out a correctly-formatted log entry.

    @param cache_name The name of the cache where the event
        occurred. "L1" or "L2"

    @param status The kind of cache event. "SW", "HIT", or
        "MISS"

    @param pc The program counter of the memory
        access instruction

    @param addr The memory address being accessed.

    @param row The cache row or set number where the data
        is stored.
*/
void print_log_entry(const string &cache_name, const string &status, int pc, int addr, int row) {
    cout << left << setw(8) << cache_name + " " + status <<  right <<
        " pc:" << setw(5) << pc <<
        "\taddr:" << setw(5) << addr <<
        "\trow:" << setw(4) << row << endl;
}

// Cache Class
class CacheBlock {
public:
    int tag;
    bool valid;
    int lastUsed; // For LRU
    int data;

    CacheBlock() : tag(-1), valid(false), lastUsed(0), data(0) {}
};

class Cache {
private:
    int size;
    int associativity;
    int blocksize;
    int numRows;
    vector<vector<CacheBlock>> rows;
    int lruCounter; // Counter to manage LRU

    // Utility function to find the LRU block index
    int findLRUBlockIndex(int rowIndex) {
        int lruIndex = 0, minUsed = rows[rowIndex][0].lastUsed;
        for (int i = 1; i < associativity; ++i) {
            if (rows[rowIndex][i].lastUsed < minUsed) {
                lruIndex = i;
                minUsed = rows[rowIndex][i].lastUsed;
            }
        }
        return lruIndex;
    }

public:
    Cache(int size, int associativity, int blocksize) 
    : size(size), associativity(associativity), blocksize(blocksize), lruCounter(0) {
        numRows = size / (associativity * blocksize);
        rows.resize(numRows);

        for (int i = 0; i < numRows; ++i) {
            rows[i].resize(associativity);
        }
    }

    int getNumRows() { return numRows; }

    // Function to access cache and update LRU
    pair<bool, int> accessCache(int address, int& data, bool isWrite) {
        int offsetBits = log2(blocksize);
        int indexBits = log2(numRows);
        int index = (address >> offsetBits) & ((1 << indexBits) - 1);
        int tag = address >> (offsetBits + indexBits);
        bool hit = false;

        // Search for tag in the cache row
        for (int i = 0; i < associativity; ++i) {
            if (rows[index][i].valid && rows[index][i].tag == tag) {
                if (isWrite) {
                    rows[index][i].data = data;
                } else {
                    data = rows[index][i].data;
                }
                rows[index][i].lastUsed = ++lruCounter;
                hit = true;
                return {hit, index};
            }
        }

        if (!hit) {
            // Handle cache miss
            int lruIndex = findLRUBlockIndex(index);
            rows[index][lruIndex].valid = true;
            rows[index][lruIndex].tag = tag;
            rows[index][lruIndex].lastUsed = ++lruCounter;

            if (isWrite) {
                rows[index][lruIndex].data = data;
            } else {
                data = -1; // Assume default value for fetched data
            }
            return {hit, index};
        }

        return {hit, index};
    }

    // Function to write data to cache (write-through)
    void writeThrough(int address, int data, int& rowIndex) {
        auto result = accessCache(address, data, true);
        rowIndex = result.second;
    }

    // Utility function to display cache configuration
    void displayConfig() const {
        cout << "Cache Configuration:" << endl;
        cout << "Size: " << size << ", Associativity: " << associativity << ", Blocksize: " << blocksize << ", Number of Rows: " << numRows << endl;
    }
};

Cache L1Cache(1, 1, 1); // Default initialization, will be overwritten
Cache L2Cache(1, 1, 1); // Default initialization, if needed

//Project 1 Code
// Some helpful constant values that we'll be using.
size_t const static NUM_REGS = 8;
size_t const static MEM_SIZE = 1<<13;
size_t const static REG_SIZE = 1<<16;

/*
    Loads an E20 machine code file into the list
    provided by mem. We assume that mem is
    large enough to hold the values in the machine
    code file.

    @param f Open file to read from
    @param mem Array represetnting memory into which to read program
*/
void load_machine_code(ifstream &f, uint16_t mem[]) {
    regex machine_code_re("^ram\\[(\\d+)\\] = 16'b(\\d+);.*$");
    size_t expectedaddr = 0;
    string line;
    while (getline(f, line)) {
        smatch sm;
        if (!regex_match(line, sm, machine_code_re)) {
            cerr << "Can't parse line: " << line << endl;
            exit(1);
        }
        size_t addr = stoi(sm[1], nullptr, 10);
        uint16_t instr = stoi(sm[2], nullptr, 2);
        if (addr != expectedaddr) {
            cerr << "Memory addresses encountered out of sequence: " << addr << endl;
            exit(1);
        }
        if (addr >= MEM_SIZE) {
            cerr << "Program too big for memory" << endl;
            exit(1);
        }
        expectedaddr ++;
        mem[addr] = instr;
    }
}

/*
    Prints the current state of the simulator, including
    the current program counter, the current register values,
    and the first memquantity elements of memory.

    @param pc The final value of the program counter
    @param regs Final value of all registers
    @param memory Final value of memory
    @param memquantity How many words of memory to dump
*/
void print_state(unsigned pc, uint16_t regs[], uint16_t memory[], size_t memquantity) {
    cout << setfill(' ');
    cout << "Final state:" << endl;
    cout << "\tpc=" <<setw(5)<< pc << endl;

    for (size_t reg=0; reg<NUM_REGS; reg++)
        cout << "\t$" << reg << "="<<setw(5)<<regs[reg]<<endl;

    cout << setfill('0');
    bool cr = false;
    for (size_t count=0; count<memquantity; count++) {
        cout << hex << setw(4) << memory[count] << " ";
        cr = true;
        if (count % 8 == 7) {
            cout << endl;
            cr = false;
        }
    }
    if (cr)
        cout << endl;
}

int16_t sign_extend_7bit(uint16_t imm) {
    if (imm >> 6)  // If the most significant bit is 1 (negative)
        return -64 + (imm & 0b111111); // Sign-extend by subtracting 64
    return imm;
}

//INSTRUCTION SET
//3.1 INSTRUCTIONS WITH 3 REGISTER ARGUMENTS
//3.1.1 add $regDst, $regSrcA, $regSrcB
void add(uint16_t regDst, uint16_t regSrcA, uint16_t regSrcB, uint16_t regs[]) {
    if(regDst != 0) //can't change reg0 so do nothing
        regs[regDst] = (regs[regSrcA] + regs[regSrcB]) % REG_SIZE; //%REG_SIZE for wrap around
}
//3.1.2 sub $regDst, $regSrcA, $regSrcB
void sub(uint16_t regDst, uint16_t regSrcA, uint16_t regSrcB, uint16_t regs[]) {
    if(regDst != 0) //can't change reg0 so do nothing
        regs[regDst] = (regs[regSrcA] - regs[regSrcB]) % REG_SIZE; //%REG_SIZE for wrap around
}
//3.1.3 or $regDst, $regSrcA, $regSrcB
void or_instr(uint16_t regDst, uint16_t regSrcA, uint16_t regSrcB, uint16_t regs[]) {
    if(regDst != 0) //can't change reg0 so do nothing
        regs[regDst] = regs[regSrcA] | regs[regSrcB];
}
//3.1.4 and $regDst, $regSrcA, $regSrcB
void and_instr(uint16_t regDst, uint16_t regSrcA, uint16_t regSrcB, uint16_t regs[]) {
    if(regDst != 0) //can't change reg0 so do nothing
        regs[regDst] = regs[regSrcA] & regs[regSrcB];
}
//3.1.5 slt $regDst, $regSrcA, $regSrcB
void slt(uint16_t regDst, uint16_t regSrcA, uint16_t regSrcB, uint16_t regs[]) {
    if(regDst != 0) //can't change reg0 so do nothing
        regs[regDst] = (regs[regSrcA] < regs[regSrcB]) ? 1 : 0;
}
//3.1.6 jr $reg
void jr(unsigned& pc, uint16_t reg, uint16_t regs[]) {
    pc = regs[reg] % MEM_SIZE; // Jump with wraparound
}

//3.2 INSTRUCTIONS WITH 2 REGISTER ARGUMENTS
//3.2.1 slti $regDst, $regSrc, imm
void slti(uint16_t regDst, uint16_t regSrc, uint16_t imm, uint16_t regs[]) {
    int16_t signedImm = sign_extend_7bit(imm);
    if (regDst != 0) // can't change reg0
        regs[regDst] = (static_cast<int32_t>(regs[regSrc]) < signedImm) ? 1 : 0;
}
//3.2.2 lw $regDst, imm($regAddr)

void lw(uint16_t regDst, uint16_t regAddr, uint16_t imm, uint16_t memory[], uint16_t regs[], Cache &L1Cache, Cache *L2Cache, unsigned pc) {
    uint16_t effectiveAddress = (regs[regAddr] + imm) % MEM_SIZE;
    int data;
    int rowIndex, blockIndex;
    auto result = L1Cache.accessCache(effectiveAddress, data, false); // Read operation

    if (result.first) { // L1 Cache hit
        regs[regDst] = data;
        print_log_entry("L1", "HIT", pc, effectiveAddress, result.second);
    } else { // L1 Cache miss
        if (L2Cache) { // Check L2 cache if it exists
            auto L2Result = L2Cache->accessCache(effectiveAddress, data, false);
            if (L2Result.first) {
                regs[regDst] = data;
                print_log_entry("L2", "HIT", pc, effectiveAddress, L2Result.second);
            } else {
                regs[regDst] = memory[effectiveAddress]; // Load from memory
                print_log_entry("L2", "MISS", pc, effectiveAddress, L2Result.second);
                L2Cache->writeThrough(effectiveAddress, regs[regDst], rowIndex); // Update L2 cache
                print_log_entry("L2", "SW", pc, effectiveAddress, rowIndex);
            }
        } else {
            regs[regDst] = memory[effectiveAddress]; // Load from memory
        }
        L1Cache.writeThrough(effectiveAddress, regs[regDst], rowIndex); // Update L1 cache
        print_log_entry("L1", "MISS", pc, effectiveAddress, rowIndex);
    }
}
//3.2.3 sw $regSrc, imm($regAddr)
void sw(uint16_t regSrc, uint16_t regAddr, uint16_t imm, uint16_t memory[], uint16_t regs[], Cache &L1Cache, Cache *L2Cache, unsigned pc) {
    uint16_t effectiveAddress = (regs[regAddr] + imm) % MEM_SIZE;
    int rowIndex, blockIndex;
    memory[effectiveAddress] = regs[regSrc]; // Store to memory first
    L1Cache.writeThrough(effectiveAddress, regs[regSrc], rowIndex); // Update L1 cache
    print_log_entry("L1", "SW", pc, effectiveAddress, rowIndex);
    if (L2Cache) {
        L2Cache->writeThrough(effectiveAddress, regs[regSrc], rowIndex); // Update L2 cache if it exists
        print_log_entry("L2", "SW", pc, effectiveAddress, rowIndex);
    }
}
//3.2.4 jeq $regA, $regB, imm
void jeq(uint16_t regA, uint16_t regB, int16_t imm, unsigned& pc, uint16_t regs[]) {
    imm = sign_extend_7bit(imm); // sign_extend_7bit function
    pc = (regs[regA] == regs[regB]) ? (pc + imm + 1) % MEM_SIZE : (pc + 1) % MEM_SIZE;
}
//3.2.5 addi $regDst, $regSrc, imm
void addi(uint16_t regDst, uint16_t regSrc, int16_t imm, uint16_t regs[]) {
    imm = sign_extend_7bit(imm);
    if (regDst != 0) // can't change reg0
        regs[regDst] = (regs[regSrc] + imm) % REG_SIZE; // Using modular arithmetic for wrap-around
}

//3.3 INSTRUCTIONS WITH NO REGISTER ARGUMENTS
//3.3.1 j imm
void j(unsigned& pc, int imm) {
    pc = imm % MEM_SIZE; // Jump with wraparound
}
//3.3.2 jal imm
void jal(unsigned& pc, uint16_t regs[], int imm) {
    regs[7] = (pc + 1) % MEM_SIZE; // Save return address with wraparound
    pc = imm % MEM_SIZE; // Jump with wraparound
}

void execute_instruction(uint16_t instr, unsigned& pc, uint16_t regs[], uint16_t memory[], bool& running, Cache &L1Cache, Cache *L2CachePtr = nullptr) {
    uint16_t opcode = instr >> 13; //opcode is first 3 bits

    if (opcode == 0) { //Instructions with three register arguments
        uint16_t regSrcA  = (instr >> 10) & 7; //bits 10-12
        uint16_t regSrcB = (instr >> 7) & 7; //bit 7-9
        uint16_t regDst = (instr >> 4) & 7; //bits 4-6
        uint16_t choice = instr & 0b1111; //last 4 bits
        if(choice == 0) { //add
            add(regDst, regSrcA, regSrcB, regs);
            pc = (pc + 1) % MEM_SIZE;
        } else if (choice == 1){ //sub
            sub(regDst, regSrcA, regSrcB, regs);
            pc = (pc + 1) % MEM_SIZE;
        } else if (choice == 2){ //or
            or_instr(regDst, regSrcA, regSrcB, regs);
            pc = (pc + 1) % MEM_SIZE;
        } else if (choice == 3){ //and
            and_instr(regDst, regSrcA, regSrcB, regs);
            pc = (pc + 1) % MEM_SIZE;
        } else if (choice == 4) { //slt
            slt(regDst, regSrcA, regSrcB, regs);
            pc = (pc + 1) % MEM_SIZE;
        } else if (choice == 8) { //jr
            jr(pc, regSrcA, regs);
        }
    } else if (opcode == 1) { //addi
        uint16_t regSrc = (instr >> 10) & 7; //bits 10-12
        uint16_t regDst = (instr >> 7) & 7; //bits 7-9
        uint16_t imm = instr & 0b1111111;  //7 bit immediate
        addi(regDst, regSrc, imm, regs);
        pc = (pc + 1) % MEM_SIZE;;
    } else if (opcode == 2) { //j
        uint16_t imm = instr & 0x1FFF; //13 bit immediate
        if(imm == pc) //it's a halt function
            running = false;
        else //do normal jump
            j(pc, imm);
    } else if (opcode == 3) { //jal
        uint16_t imm = instr & 0x1FFF; //13 bit immediate
        jal(pc, regs, imm);
    } else if (opcode == 4) { //lw
        uint16_t regAddr = (instr >> 10) & 7; //bits 10-12
        uint16_t regDst = (instr >> 7) & 7; //bit 7-9
        uint16_t imm = instr & 0b1111111; //7 bit immediate
        lw(regDst, regAddr, imm, memory, regs, L1Cache, L2CachePtr, pc);
        pc = (pc + 1) % MEM_SIZE;
    } else if (opcode == 0x5) { //sw
        uint16_t regAddr = (instr >> 10) & 7; //bits 10-12
        uint16_t regSrc = (instr >> 7) & 7; //bit 7-9
        uint16_t imm = instr & 0b1111111; //7 bit immediate
        sw(regSrc, regAddr, imm, memory, regs, L1Cache, L2CachePtr, pc);
        pc = (pc + 1) % MEM_SIZE;
    } else if (opcode == 6) { //jeq
        uint16_t regA = (instr >> 10) & 7; //bits 10-12
        uint16_t regB = (instr >> 7) & 7; //bit 7-9
        uint16_t imm = instr & 0b1111111; //7 bit immediate
        jeq(regA, regB, imm, pc, regs);
    } else if (opcode == 7) { //slti
        uint16_t regSrc = (instr >> 10) & 7; //bits 10-12
        uint16_t regDst = (instr >> 7) & 7; //bit 7-9
        uint16_t imm = instr & 0b1111111; //7 bit immediate
        slti(regDst, regSrc, imm, regs);
        pc = (pc + 1) % MEM_SIZE;
    } else { //opcode was wrong
        cerr << "Unknown instruction: " << instr << endl;
        exit(1);
    }
}

/**
    Main function
    Takes command-line args as documented below
*/
int main(int argc, char *argv[]) {
    /*
        Parse the command-line arguments
    */
    char *filename = nullptr;
    bool do_help = false;
    bool arg_error = false;
    string cache_config;
    for (int i=1; i<argc; i++) {
        string arg(argv[i]);
        if (arg.rfind("-",0)==0) {
            if (arg== "-h" || arg == "--help")
                do_help = true;
            else if (arg=="--cache") {
                i++;
                if (i>=argc)
                    arg_error = true;
                else
                    cache_config = argv[i];
            }
            else
                arg_error = true;
        } else {
            if (filename == nullptr)
                filename = argv[i];
            else
                arg_error = true;
        }
    }
    /* Display error message if appropriate */
    if (arg_error || do_help || filename == nullptr) {
        cerr << "usage " << argv[0] << " [-h] [--cache CACHE] filename" << endl << endl;
        cerr << "Simulate E20 cache" << endl << endl;
        cerr << "positional arguments:" << endl;
        cerr << "  filename    The file containing machine code, typically with .bin suffix" << endl<<endl;
        cerr << "optional arguments:"<<endl;
        cerr << "  -h, --help  show this help message and exit"<<endl;
        cerr << "  --cache CACHE  Cache configuration: size,associativity,blocksize (for one"<<endl;
        cerr << "                 cache) or"<<endl;
        cerr << "                 size,associativity,blocksize,size,associativity,blocksize"<<endl;
        cerr << "                 (for two caches)"<<endl;
        return 1;
    }

    ifstream f(filename);
    if (!f.is_open()) {
        cerr << "Can't open file " << filename << endl;
        return 1;
    }

    // Load f and parse using load_machine_code
    uint16_t regs[NUM_REGS] = {0}; //create the regs set to 0
    uint16_t memory[MEM_SIZE] = {0}; //create the memory set to 0
    load_machine_code(f, memory); 

    Cache *L2CachePtr = nullptr;
    /* parse cache config */
    if (cache_config.size() > 0) {
        vector<int> parts;
        size_t pos;
        size_t lastpos = 0;
        while ((pos = cache_config.find(",", lastpos)) != string::npos) {
            parts.push_back(stoi(cache_config.substr(lastpos,pos)));
            lastpos = pos + 1;
        }
        parts.push_back(stoi(cache_config.substr(lastpos)));
        if (parts.size() == 3) {
            int L1size = parts[0];
            int L1assoc = parts[1];
            int L1blocksize = parts[2];
            // TODO: execute E20 program and simulate one cache here
            L1Cache = Cache(L1size, L1assoc, L1blocksize);
            print_cache_config("L1", L1size, L1assoc, L1blocksize, L1Cache.getNumRows());
        } else if (parts.size() == 6) {
            int L1size = parts[0];
            int L1assoc = parts[1];
            int L1blocksize = parts[2];
            int L2size = parts[3];
            int L2assoc = parts[4];
            int L2blocksize = parts[5];
            // TODO: execute E20 program and simulate two caches here
            L1Cache = Cache(L1size, L1assoc, L1blocksize);
            L2Cache = Cache(L2size, L2assoc, L2blocksize);
            L2CachePtr = &L2Cache; // Update the pointer
            print_cache_config("L1", L1size, L1assoc, L1blocksize, L1Cache.getNumRows());
            print_cache_config("L2", L2size, L2assoc, L2blocksize, L2Cache.getNumRows());
        } else {
            cerr << "Invalid cache config"  << endl;
            return 1;
        }
    }

    unsigned pc = 0;
    bool running = true;
    while (running) {
        uint16_t instr = memory[pc % MEM_SIZE];
        execute_instruction(instr, pc, regs, memory, running, L1Cache, L2CachePtr);
    }

    return 0;
}
//ra0Eequ6ucie6Jei0koh6phishohm9