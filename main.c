//shift implements as I type

/*
Monitor 1 - PC
Monitor 2 - Instruction
Monitor 3 - rs
Monitor 4 - rt
Monitor 5 - Write Reg
Monitor 6 - Write data
Monitor 7 - rs data
Monitor 8 - rt data
Monitor 9 - ALU out
Monitor 10 - BTA
Monitor 11 - Mem addr
Monitor 12 - Mem write data
Monitor 13 - Mem read data
Monitor 14 - Control signals
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#include <time.h>

#define mmp 256      /* max memory positions */
#define lbl_max 256  /* max label positions */
#define MAX_LINE_LENGTH 256
#define MAX_STRING_LENGTH 256

/* Function declarations */
void print_monitors(int endd);
int lbl_trans(char* label);
void update(void);
void instr_reg(int line);
void control_unit(void);
int target_calc(void);
void reg_file(void);
void ALU(void);
void memory(void);
void brnch(void);
void jmp(void);
void monitors(void);
void init_out(void);
void hazardDetectionAndForwarding(void);
void IFflush(int fl);
void bubbles(void);
void preparser(void);
int starter(void);
void fillMem(void);
void earlyBranch(void);
int mem_trans(unsigned int addr);
long msbPC(void);

char* mipsRegisters[33] = {
        "zero", "at", "v0", "v1", "a0", "a1", "a2", "a3",
        "t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7",
        "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7",
        "t8", "t9", "k0", "k1", "gp", "sp", "fp", "ra", "-"
};

int reg[33];

typedef struct {
    int rs;
    int rt;
    int rd;
    int wr;
    int target;
    int PC1;
    char instr[MAX_STRING_LENGTH];
    int readA;
    int readB;
    int regdst;
    int branch;
    int memread;
    int memwrite;
    int memtoreg;
    int regwrite;
    int ALUsrc;
    int ALUsrcA;
    int ALUsrcB;
    int fw;
    int immed;
    int aluop;
    int aluout;
    int mem_in;
    int mem_out;
    int write_data;
    int zero;
    char string_lbl[MAX_STRING_LENGTH];
    char opcode[MAX_STRING_LENGTH];
    char type[MAX_STRING_LENGTH];
} pipeline;

pipeline IFID, IDEX, EXMEM, MEMWB, EXT;

long memAddress[mmp];
long MEM[mmp];

char label_nm[lbl_max][MAX_STRING_LENGTH];
int LBL[lbl_max];
int label_count = 0;

clock_t start_time, end_time;
double userTime;

int PC = 0, nextPC;
int mainline;
int EOF_flag = 0;
int ifflush = 0;
int stall = 0;
int hazard, forwarding;

int cyc_to_print[100];
int cyc_count = 0;

/* Control signals */
int regdst, jump, branch, memread, memtoreg, memwrite, ALUsrc, regwrite, zero;
int aluop;

/* Monitors */
int wr, write_data, readA, readB, aluout, target, mem_in, mem_out;
char instr[MAX_STRING_LENGTH], opcode[MAX_STRING_LENGTH], type[MAX_STRING_LENGTH], instr_evicted[MAX_STRING_LENGTH];

char file_name[MAX_STRING_LENGTH];
int rs, rt, rd, address, immed, cycles = 1;

/* Utility functions */
int hex_dec(char* hexString) {
    int decimalValue;
    sscanf(hexString, "%x", &decimalValue);
    return decimalValue;
}

void intToHex(int value, char* result) {
    /* Ensure the value fits within 32 bits (4 bytes) */
    value &= 0xFFFFFFFF;
    sprintf(result, "%08X", value);
}

void intToBinary(unsigned int num, char* result) {
    /* Ensure the input number is within the range [0, 15] */
    num = num & 0xF;

    /* Convert the integer to its binary representation */
    for (int i = 3; i >= 0; i--) {
        result[3-i] = ((num >> i) & 1) ? '1' : '0';
    }
    result[4] = '\0';
}

void trim(char* in, char* out) {
    int l = strlen(in);
    int found = 0;
    int outIdx = 0;

    for (int i = 0; i < l; i++) {
        if (in[i] == '0' && !found) {
            continue;
        } else {
            if (in[i] != '0' || found) {
                found = 1;
                out[outIdx++] = in[i];
            }
        }
    }
    out[outIdx] = '\0';

    if (outIdx == 0) {
        strcpy(out, "0");
    }
}

int stringToInt(const char* str) {
    int result;
    char* endptr;

    result = strtol(str, &endptr, 10);
    if (*endptr != '\0') {
        printf("%s\n", str);
        fprintf(stderr, "Invalid argument\n");
        return 0;
    }

    return result;
}

unsigned int directToInt(char* hex) {
    unsigned int sum = 0;

    for (int i = 0; i < 8; i++) {
        switch (hex[i]) {
            case 'F':
                sum += pow(2, (((8-i)*4)-1));
                sum += pow(2, (((8-i)*4)-2));
                sum += pow(2, (((8-i)*4)-3));
                sum += pow(2, (((8-i)*4)-4));
                break;
            case 'E':
                sum += pow(2, (((8-i)*4)-1));
                sum += pow(2, (((8-i)*4)-2));
                sum += pow(2, (((8-i)*4)-3));
                break;
            case 'D':
                sum += pow(2, (((8-i)*4)-1));
                sum += pow(2, (((8-i)*4)-2));
                sum += pow(2, (((8-i)*4)-4));
                break;
            case 'C':
                sum += pow(2, (((8-i)*4)-1));
                sum += pow(2, (((8-i)*4)-2));
                break;
            case 'B':
                sum += pow(2, (((8-i)*4)-1));
                sum += pow(2, (((8-i)*4)-3));
                sum += pow(2, (((8-i)*4)-4));
                break;
            case 'A':
                sum += pow(2, (((8-i)*4)-1));
                sum += pow(2, (((8-i)*4)-3));
                break;
            case '9':
                sum += pow(2, (((8-i)*4)-1));
                sum += pow(2, (((8-i)*4)-4));
                break;
            case '8':
                sum += pow(2, (((8-i)*4)-1));
                break;
            case '7':
                sum += pow(2, (((8-i)*4)-2));
                sum += pow(2, (((8-i)*4)-3));
                sum += pow(2, (((8-i)*4)-4));
                break;
            case '6':
                sum += pow(2, (((8-i)*4)-2));
                sum += pow(2, (((8-i)*4)-3));
                break;
            case '5':
                sum += pow(2, (((8-i)*4)-2));
                sum += pow(2, (((8-i)*4)-4));
                break;
            case '4':
                sum += pow(2, (((8-i)*4)-2));
                break;
            case '3':
                sum += pow(2, (((8-i)*4)-3));
                sum += pow(2, (((8-i)*4)-4));
                break;
            case '2':
                sum += pow(2, (((8-i)*4)-3));
                break;
            case '1':
                sum += pow(2, (((8-i)*4)-4));
                break;
        }
    }

    return sum;
}

char* parser(int line) {
    FILE* fl;
    static char com[MAX_LINE_LENGTH];

    EOF_flag = 0;
    fl = fopen(file_name, "r");
    if (!fl) {
        printf("Error: Could not open file %s\n", file_name);
        exit(-1);
    }

    int j = 1;
    // Initialize com to empty string to avoid undefined behavior
    com[0] = '\0';

    while (j <= line) {
        if (fgets(com, MAX_LINE_LENGTH, fl) == NULL) {
            EOF_flag = 1;
            break;
        }
        j++;
    }

    int len = strlen(com);
    if (len > 0 && com[len-1] == '\n') {
        com[len-1] = '\0';
    }

    fclose(fl);
    return com;
}

void formater(char* inp, char* out) { /* Removes tabs, new lines, and spaces */
    int len = strlen(inp);
    int outIdx = 0;

    for (int i = 0; i < len; i++) {
        if (inp[i] == '#') {
            break;
        } else {
            if (inp[i] != ' ' && inp[i] != '\t' && inp[i] != '\n') {
                out[outIdx++] = inp[i];
            }
        }
    }
    out[outIdx] = '\0';
}

void deformater(char* in, char* inop, char* out) {
    out[0] = '\0';

    if (in[0] == 'j') {
        out[0] = 'j';
        out[1] = ' ';
        strcpy(out + 2, in + 1);
        return;
    }

    if (strcmp(inop, "add") == 0 || strcmp(inop, "addu") == 0 || strcmp(inop, "and") == 0 ||
        strcmp(inop, "nor") == 0 || strcmp(inop, "or") == 0 || strcmp(inop, "slt") == 0 ||
        strcmp(inop, "sltu") == 0 || strcmp(inop, "sub") == 0 || strcmp(inop, "subu") == 0) { /* R-TYPE */
        int outIdx = 0;
        for (int i = 0; i < strlen(in); i++) {
            out[outIdx++] = in[i];
            if (in[i+1] == '$') {
                out[outIdx++] = ' ';
            }
        }
        out[outIdx] = '\0';
        return;
    }

    if (strcmp(inop, "addi") == 0 || strcmp(inop, "addui") == 0 || strcmp(inop, "addiu") == 0 ||
        strcmp(inop, "andi") == 0 || strcmp(inop, "ori") == 0 || strcmp(inop, "slti") == 0 ||
        strcmp(inop, "sltiu") == 0 || strcmp(inop, "sltui") == 0 || strcmp(inop, "sll") == 0 ||
        strcmp(inop, "srl") == 0 || strcmp(inop, "beq") == 0 || strcmp(inop, "bne") == 0) { /* I[...] */
        int comma = 0, dol = 0;
        int outIdx = 0;
        for (int i = 0; i < strlen(in); i++) {
            out[outIdx++] = in[i];
            if (in[i+1] == '$') {
                out[outIdx++] = ' ';
                dol++;
            }
            if (in[i] == ',') {
                comma++;
                if (comma == 2) {
                    out[outIdx++] = ' ';
                }
            }
        }
        out[outIdx] = '\0';
        return;
    }

    if (strcmp(inop, "lw") == 0 || strcmp(IFID.opcode, "sw") == 0) { /* SPECIAL-I-TYPE */
        int i = 0;
        int outIdx = 0;
        while (in[i+1] != '$') {
            out[outIdx++] = in[i];
            i++;
        }
        out[outIdx++] = in[i];
        i++;
        out[outIdx++] = ' ';
        while (in[i] != ',') {
            out[outIdx++] = in[i];
            i++;
        }
        out[outIdx++] = in[i]; /* comma */
        i++;
        out[outIdx++] = ' ';
        while (i < strlen(in)) {
            out[outIdx++] = in[i];
            i++;
        }
        out[outIdx] = '\0';
        return;
    }

    /* If we get here, something went wrong */
    out[0] = '\0';
}

int starter() { /* Finds the line where main starts */
    int line = 0;
    char com[MAX_LINE_LENGTH];
    char temp[6];

    while (1) {
        strcpy(com, parser(line));

        if (strlen(com) >= 5) {
            strncpy(temp, com, 5);
            temp[5] = '\0';
            if (strcmp(temp, "main:") == 0) {
                return line++;
            }
        }

        line++;
    }
}

void submit_label(char* name, int pointer) {
    if (label_count == lbl_max) {
        exit(-6);
    }

    strcpy(label_nm[label_count], name);
    LBL[label_count] = pointer;
    label_count++;
}

void preparser() {
    FILE* fout;
    int i = 0, stalls = 0;
    char line[MAX_LINE_LENGTH];
    char formatted_line[MAX_LINE_LENGTH];
    int isLabel;
    int empt = 0;

    fout = fopen("clean_input.txt", "w");
    if (!fout) {
        exit(-5);
    }

    mainline = starter();
    for (i = 0; i <= mainline; i++) {
        fprintf(fout, "%s\n", parser(i));
    }

    do {
        isLabel = 0;
        strcpy(line, parser(i));
        formater(line, formatted_line);

        if (strlen(formatted_line) > 0) {
            if (formatted_line[strlen(formatted_line)-1] == ':') {
                char lbl_bd[MAX_STRING_LENGTH] = "";
                int lbl_ln = i - empt - mainline - 1 - label_count; /* To be removed */
                strncpy(lbl_bd, formatted_line, strlen(formatted_line)-1);
                lbl_bd[strlen(formatted_line)-1] = '\0';
                submit_label(lbl_bd, lbl_ln);
            } else {
                fprintf(fout, "%s\n", formatted_line);
            }
        } else {
            empt++;
        }
        i++;
    } while (!EOF_flag);

    fprintf(fout, "sll$zero,$zero,0\n");
    fprintf(fout, "sll$zero,$zero,1\n");
    fprintf(fout, "sll$zero,$zero,0");

    strcpy(file_name, "clean_input.txt");
    fclose(fout);
}

int reg_trans(char* alias) { /* Register translation from alias to number */
    for (int i = 0; i < 32; i++) {
        if (strcmp(mipsRegisters[i], alias) == 0) {
            return i;
        }
    }
    return -1; /* Return -1 if the alias is not found */
}

void j_type(char* com) { /* NOT USED */
    char address_str[MAX_STRING_LENGTH] = "";
    char rs_str[MAX_STRING_LENGTH] = "";
    char label_str[MAX_STRING_LENGTH] = "";
    char temp_hex[MAX_STRING_LENGTH];

    strcpy(IFID.type, "J");

    switch (com[1]) {
        case 'a': /* jal */
            strncpy(address_str, com + 3, strlen(com) - 3);
            address_str[strlen(com) - 3] = '\0';
            reg[reg_trans("ra")] = PC; /* Save $ra */
            strcpy(opcode, "jal");
            break;

        case 'r': /* jr$ */
            strncpy(rs_str, com + 3, strlen(com) - 3);
            rs_str[strlen(com) - 3] = '\0';
            intToHex(reg[reg_trans(rs_str)], temp_hex);
            strcpy(address_str, temp_hex);
            strcpy(opcode, "jr");
            break;

        default: /* j */
            strncpy(label_str, com + 1, strlen(com) - 1);
            label_str[strlen(com) - 1] = '\0';
            strcpy(opcode, "j");
            break;
    }

    address = LBL[lbl_trans(label_str)];
    IFID.rs = 32;
    IFID.rt = 32;
    IFID.rd = 32;
}

void r_type(char* com) {
    int i;
    char rs_str[MAX_STRING_LENGTH] = "";
    char rt_str[MAX_STRING_LENGTH] = "";
    char rd_str[MAX_STRING_LENGTH] = "";
    strcpy(IFID.type, "R");
    strcpy(IFID.string_lbl, "-");

    i = 0;
    do {
        i++;
    } while (com[i] != '$');
    /* Opcode done */
    i++;
    /* rd start */
    int rdIdx = 0;
    do {
        rd_str[rdIdx++] = com[i];
        i++;
    } while (com[i] != ',');
    rd_str[rdIdx] = '\0';
    /* rd done */
    i++;
    i++;
    /* rs start */
    int rsIdx = 0;
    do {
        rs_str[rsIdx++] = com[i];
        i++;
    } while (com[i] != ',');
    rs_str[rsIdx] = '\0';
    /* rs done */
    i++;
    i++;
    /* rt start */
    int rtIdx = 0;
    do {
        rt_str[rtIdx++] = com[i];
        i++;
    } while (i < strlen(com));
    rt_str[rtIdx] = '\0';

    IFID.rs = reg_trans(rs_str);
    IFID.rt = reg_trans(rt_str);
    IFID.rd = reg_trans(rd_str);
    IFID.wr = reg_trans(rd_str);
}

void b_type(char* com) {
    int i;
    char rs_str[MAX_STRING_LENGTH] = "";
    char rt_str[MAX_STRING_LENGTH] = "";
    char label_str[MAX_STRING_LENGTH] = "";
    strcpy(IFID.type, "B");

    i = 0;
    do {
        i++;
    } while (com[i] != '$');
    /* Opcode done */
    i++;
    /* rt start */
    int rtIdx = 0;
    do {
        rt_str[rtIdx++] = com[i];
        i++;
    } while (com[i] != ',');
    rt_str[rtIdx] = '\0';
    /* rt done */
    i++;
    i++;
    /* rs start */
    int rsIdx = 0;
    do {
        rs_str[rsIdx++] = com[i];
        i++;
    } while (com[i] != ',');
    rs_str[rsIdx] = '\0';
    /* rs done */
    i++;
    /* label start */
    int lblIdx = 0;
    do {
        label_str[lblIdx++] = com[i];
        i++;
    } while (i < strlen(com));
    label_str[lblIdx] = '\0';

    IFID.rs = reg_trans(rs_str);
    IFID.rt = reg_trans(rt_str);
    IFID.wr = 0;
    IFID.target = LBL[lbl_trans(label_str)];
    strcpy(IFID.string_lbl, label_str);
    IFID.rd = 32;
}

void i_type(char* com) {
    int i;
    char rs_str[MAX_STRING_LENGTH] = "";
    char rt_str[MAX_STRING_LENGTH] = "";
    char immed_str[MAX_STRING_LENGTH] = "";
    strcpy(IFID.type, "I");
    strcpy(IFID.string_lbl, "-");

    i = 0;
    do {
        i++;
    } while (com[i] != '$');
    /* Opcode done */
    i++;
    /* rt start */
    int rtIdx = 0;
    do {
        rt_str[rtIdx++] = com[i];
        i++;
    } while (com[i] != ',');
    rt_str[rtIdx] = '\0';
    /* rt done */
    i++;
    i++;
    /* rs start */
    int rsIdx = 0;
    do {
        rs_str[rsIdx++] = com[i];
        i++;
    } while (com[i] != ',');
    rs_str[rsIdx] = '\0';
    /* rs done */
    i++;
    /* immed start */
    int immedIdx = 0;
    do {
        immed_str[immedIdx++] = com[i];
        i++;
    } while (i < strlen(com));
    immed_str[immedIdx] = '\0';

    IFID.rs = reg_trans(rs_str);
    IFID.rt = reg_trans(rt_str);
    IFID.wr = reg_trans(rt_str);

    if (immed_str[0] == '0' && immed_str[1] == 'x') {
        char temp[MAX_STRING_LENGTH] = "";
        strcpy(temp, immed_str + 2);
        IFID.immed = hex_dec(temp);
    } else {
        IFID.immed = stringToInt(immed_str);
    }
    IFID.rd = 32;
}

void special_i_type(char* com) {
    int i;
    char rs_str[MAX_STRING_LENGTH] = "";
    char rt_str[MAX_STRING_LENGTH] = "";
    char immed_str[MAX_STRING_LENGTH] = "";
    strcpy(IFID.type, "SPI");
    strcpy(IFID.string_lbl, "-");

    i = 0;
    do {
        i++;
    } while (com[i] != '$');
    /* Opcode done */
    i++;
    /* rt start */
    int rtIdx = 0;
    do {
        rt_str[rtIdx++] = com[i];
        i++;
    } while (com[i] != ',');
    rt_str[rtIdx] = '\0';
    /* rt done */
    i++; /* Skip comma */

    int immedIdx = 0;
    while (com[i] >= '0' && com[i] <= '9') {
        immed_str[immedIdx++] = com[i];
        i++;
    }
    immed_str[immedIdx] = '\0';
    /* immed done */
    i++; /* Skip parentheses */
    i++; /* Skip $ */
    /* rs start */
    int rsIdx = 0;
    do {
        rs_str[rsIdx++] = com[i];
        i++;
    } while (com[i] != ')');
    rs_str[rsIdx] = '\0';

    if (strcmp(rs_str, "pc") == 0) {
        IFID.rs = PC + 1;
    } else {
        IFID.rs = reg_trans(rs_str);
    }
    IFID.rt = reg_trans(rt_str);
    IFID.immed = stringToInt(immed_str);
    IFID.wr = reg_trans(rt_str);
    IFID.rd = 32;
}

void instr_reg(int line) {
    char com[MAX_LINE_LENGTH];
    char formatted_com[MAX_LINE_LENGTH];
    char opcd[MAX_STRING_LENGTH] = "";
    int i = 0;

    strcpy(com, parser(line));
    formater(com, formatted_com);
    strcpy(instr, formatted_com);
    strcpy(IFID.instr, formatted_com);

    PC++;
    IFID.PC1 = PC;

    printf("%s\n", formatted_com);

    if (formatted_com[0] == 'j') { /* J-TYPE */
        j_type(formatted_com);
    } else {
        i = 0;
        int opcdIdx = 0;
        do {
            opcd[opcdIdx++] = formatted_com[i];
            i++;
        } while (formatted_com[i] != '$');
        opcd[opcdIdx] = '\0';
        strcpy(IFID.opcode, opcd);
        /* Have the opcode as string */

        if (strcmp(opcd, "add") == 0 || strcmp(opcd, "addu") == 0 || strcmp(opcd, "and") == 0 ||
            strcmp(opcd, "nor") == 0 || strcmp(opcd, "or") == 0 || strcmp(opcd, "slt") == 0 ||
            strcmp(opcd, "sltu") == 0 || strcmp(opcd, "sub") == 0 || strcmp(opcd, "subu") == 0) { /* R-TYPE */
            r_type(formatted_com);
        } else {
            if (strcmp(opcd, "addi") == 0 || strcmp(opcd, "addui") == 0 || strcmp(opcd, "addiu") == 0 ||
                strcmp(opcd, "andi") == 0 || strcmp(opcd, "ori") == 0 || strcmp(opcd, "slti") == 0 ||
                strcmp(opcd, "sltiu") == 0 || strcmp(opcd, "sltui") == 0 || strcmp(opcd, "sll") == 0 ||
                strcmp(opcd, "srl") == 0) { /* I-TYPE */
                i_type(formatted_com);
            } else {
                if (strcmp(opcd, "sw") == 0 || strcmp(opcd, "lw") == 0) { /* SPECIAL-I-TYPE */
                    special_i_type(formatted_com);
                } else {
                    if (strcmp(opcd, "beq") == 0 || strcmp(opcd, "bne") == 0) { /* B-TYPE */
                        b_type(formatted_com);
                    } else {
                        exit(-2);
                    }
                }
            }
        }
    }
    /* Theoretically have opcode, rs, rt, rd, func, immed, address */
}

int target_calc() { /* Also monitor 10 */
    /* target = PC + immed; Not *4 because addresses go +1 */
    return target;
}

void control_unit() {
    /* PC++; */

    if (strcmp(IFID.instr, "sll$zero,$zero,1") == 0) {
        end_time = clock();
        userTime = (double)(end_time - start_time) / CLOCKS_PER_SEC;
        print_monitors(1);
        exit(0);
    }

    if (strcmp(IFID.opcode, "add") == 0) {
        IFID.regdst = 1;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 2; /* add */
        IFID.memwrite = 0;
        IFID.ALUsrc = 0;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "addi") == 0) {
        IFID.regdst = 0;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 2; /* add */
        IFID.memwrite = 0;
        IFID.ALUsrc = 1;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "addui") == 0 || strcmp(IFID.opcode, "addiu") == 0) {
        IFID.regdst = 0;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 7; /* addu */
        IFID.memwrite = 0;
        IFID.ALUsrc = 1;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "addu") == 0) {
        IFID.regdst = 1;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 7; /* addu */
        IFID.memwrite = 0;
        IFID.ALUsrc = 0;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    /* Continue with similar pattern for all remaining instructions... */

    if (strcmp(IFID.opcode, "and") == 0) {
        IFID.regdst = 1;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 0; /* and */
        IFID.memwrite = 0;
        IFID.ALUsrc = 0;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "andi") == 0) {
        IFID.regdst = 0;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 0; /* and */
        IFID.memwrite = 0;
        IFID.ALUsrc = 1;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "beq") == 0) {
        IFID.regdst = 0;
        IFID.branch = 1;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 6; /* sub */
        IFID.memwrite = 0;
        IFID.ALUsrc = 0;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 0;
    }

    if (strcmp(IFID.opcode, "bne") == 0) {
        IFID.regdst = 0;
        IFID.branch = 1;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 6; /* sub */
        IFID.memwrite = 0;
        IFID.ALUsrc = 0;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 0;
    }

    if (strcmp(IFID.opcode, "lw") == 0) {
        IFID.regdst = 0;
        IFID.branch = 0;
        IFID.memread = 1;
        IFID.memtoreg = 1;
        IFID.aluop = 2; /* add */
        IFID.memwrite = 0;
        IFID.ALUsrc = 1;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "nor") == 0) {
        IFID.regdst = 1;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 12; /* nor */
        IFID.memwrite = 0;
        IFID.ALUsrc = 0;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "or") == 0) {
        IFID.regdst = 1;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 1; /* or */
        IFID.memwrite = 0;
        IFID.ALUsrc = 0;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "ori") == 0) {
        IFID.regdst = 0;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 1; /* or */
        IFID.memwrite = 0;
        IFID.ALUsrc = 1;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "slt") == 0) {
        IFID.regdst = 1;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 3; /* slt */
        IFID.memwrite = 0;
        IFID.ALUsrc = 0;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "slti") == 0) {
        IFID.regdst = 0;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 3; /* slt */
        IFID.memwrite = 0;
        IFID.ALUsrc = 1;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "sltiu") == 0 || strcmp(IFID.opcode, "sltui") == 0) {
        IFID.regdst = 0;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 8; /* sltu */
        IFID.memwrite = 0;
        IFID.ALUsrc = 1;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "sltu") == 0) {
        IFID.regdst = 1;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 8; /* sltu */
        IFID.memwrite = 0;
        IFID.ALUsrc = 0;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "sll") == 0) {
        IFID.regdst = 0;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 5; /* sll */
        IFID.memwrite = 0;
        IFID.ALUsrc = 1;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "srl") == 0) {
        IFID.regdst = 0;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 4; /* srl */
        IFID.memwrite = 0;
        IFID.ALUsrc = 1;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "sw") == 0) {
        IFID.regdst = 0;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 1;
        IFID.aluop = 2; /* add */
        IFID.memwrite = 1;
        IFID.ALUsrc = 1;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 0;
    }

    if (strcmp(IFID.opcode, "sub") == 0) {
        IFID.regdst = 1;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 6; /* sub */
        IFID.memwrite = 0;
        IFID.ALUsrc = 0;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "subu") == 0) {
        IFID.regdst = 1;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 9; /* subu */
        IFID.ALUsrc = 0;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 1;
    }

    if (strcmp(IFID.opcode, "j") == 0 || strcmp(IFID.opcode, "jal") == 0) {
        IFID.regdst = 0;
        IFID.branch = 0;
        IFID.memread = 0;
        IFID.memtoreg = 0;
        IFID.aluop = 2; /* add */
        IFID.memwrite = 0;
        IFID.ALUsrc = 0;
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.regwrite = 0;
    }
}

void reg_file() {
    if (MEMWB.memtoreg) {
        MEMWB.write_data = MEMWB.mem_out;
    } else {
        MEMWB.write_data = MEMWB.aluout;
    }

    if (MEMWB.regdst) {
        MEMWB.wr = MEMWB.rd; /* Write register */
    } else {
        MEMWB.wr = MEMWB.rt;
    }

    if (MEMWB.regwrite) {
        reg[MEMWB.wr] = MEMWB.write_data;
    }

    IFID.readA = reg[IFID.rs];
    IFID.readB = reg[IFID.rt];
    IFID.mem_in = IFID.readB; /* Because ALU will take immed as inB */
}

void ALU() {
    int inA = IDEX.readA;
    int inB;

    switch (IDEX.ALUsrcA) {
        case 0:
            inA = IDEX.readA;
            break;
        case 1:
            inA = EXMEM.aluout;
            break;
        case 2:
            inA = MEMWB.fw;
            break;
    }

    switch (IDEX.ALUsrcB) {
        case 0:
            inB = IDEX.readB;
            break;
        case 1:
            inB = EXMEM.aluout;
            break;
        case 2:
            inB = MEMWB.fw;
            break;
    }

    if (IDEX.ALUsrc) {
        inB = IDEX.immed;
    }

    switch (IDEX.aluop) {
        case 2: /* add */
            aluout = inA + inB;
            break;
        case 6: /* sub */
            aluout = inA - inB;
            break;
        case 3: /* slt */
            aluout = inA - inB;
            if (aluout < 0)
                aluout = 1;
            else
                aluout = 0;
            break;
        case 8: /* sltu */
        {
            char temp1[MAX_STRING_LENGTH], temp2[MAX_STRING_LENGTH];
            intToHex(inA, temp1);
            intToHex(inB, temp2);
            aluout = directToInt(temp1) - directToInt(temp2);
            if (aluout < 0)
                aluout = 1;
            else
                aluout = 0;
        }
            break;
        case 0: /* and */
            aluout = inA & inB;
            break;
        case 1: /* or */
            aluout = inA | inB;
            break;
        case 12: /* nor */
            aluout = ~(inA | inB);
            break;
        case 5: /* sll */
            aluout = inA;
            for (int i = 0; i < inB; i++) {
                aluout *= 2;
            }
            break;
        case 4: /* srl */
            aluout = inA;
            for (int i = 0; i < inB; i++) {
                aluout /= (int)2;
            }
            break;
        case 7: /* addu */
        {
            char temp1[MAX_STRING_LENGTH], temp2[MAX_STRING_LENGTH];
            intToHex(inA, temp1);
            intToHex(inB, temp2);
            aluout = directToInt(temp1) + directToInt(temp2);
        }
            break;
        case 9: /* subu */
        {
            char temp1[MAX_STRING_LENGTH], temp2[MAX_STRING_LENGTH];
            intToHex(inA, temp1);
            intToHex(inB, temp2);
            aluout = directToInt(temp1) - directToInt(temp2);
        }
            break;
    }

    if (aluout == 0) {
        IDEX.zero = 1;
    } else {
        IDEX.zero = 0;
    }

    IDEX.aluout = aluout;
}

long msbPC() {
    long msb = PC & (~(268435455));
    return msb;
}

void earlyBranch() {
    if (strcmp(IFID.opcode, "beq") == 0 && reg[IFID.rs] == reg[IFID.rt]) {
        PC = IDEX.target - 1;
        IFID.branch = 0;
        ifflush = 1;
    }
}

void jmp() {
    if (jump) {
        PC = address; /* Was addr+msbPC() */
    }
}

int lbl_trans(char* label) {
    // Safety check for null input
    if (!label || strlen(label) == 0) {
        printf("Warning: Empty label passed to lbl_trans\n");
        return -1;
    }

    for (int i = 0; i < lbl_max; i++) {
        // Only compare if there's actually a label at this position
        if (label_nm[i][0] != '\0' && strcmp(label_nm[i], label) == 0) {
            return i;
        }
    }
    printf("Warning: Label '%s' not found\n", label);
    return -1;
}

int mem_trans(unsigned int addr) {
    for (int i = 0; i < mmp; i++) {
        if (memAddress[i] == addr) {
            return i;
        }
    }

    // Find empty slot
    for (int i = 0; i < mmp; i++) {
        if (memAddress[i] == 0) {
            memAddress[i] = addr;
            return i;
        }
    }

    printf("Error: Out of memory in mem_trans\n");
    exit(-3);
}

void memory() {
    if (EXMEM.memread) {
        EXMEM.mem_out = MEM[mem_trans(EXMEM.aluout)];
    }

    if (EXMEM.memwrite) {
        MEM[mem_trans(EXMEM.aluout)] = EXMEM.mem_in;
    }
}

void fillMem() {
    reg[reg_trans("gp")] = hex_dec("10008000");
    reg[reg_trans("sp")] = hex_dec("7FFFFFFC");
}

void print_monitors(int endd) {
    FILE* fout;
    char hex_buffer[MAX_STRING_LENGTH];
    char formatted_output[MAX_STRING_LENGTH];

    fout = fopen("output.txt", "a");
    if (!fout) {
        exit(-4);
    }

    if (endd) {
        fprintf(fout, "\n-----Final State-----\n");
    } else {
        fprintf(fout, "\n-----Cycle %d-----\n", cycles);
    }
    fprintf(fout, "Registers:\n");

    /* PC value display */
    if ((strcmp(EXMEM.opcode, "beq") == 0 && EXMEM.zero && EXMEM.branch) ||
        (strcmp(EXMEM.opcode, "bne") == 0 && !EXMEM.zero && EXMEM.branch)) {
        intToHex(IDEX.PC1 * 4, hex_buffer);
        trim(hex_buffer, formatted_output);
        fprintf(fout, "%s\t", formatted_output);
    } else {
        intToHex((PC * 4 - 4), hex_buffer);
        trim(hex_buffer, formatted_output);
        fprintf(fout, "%s\t", formatted_output);
    }

    /* Register values */
    for (int i = 0; i < 32; i++) {
        if (reg[i] == 0) {
            fprintf(fout, "0\t");
        } else {
            intToHex(reg[i], hex_buffer);
            trim(hex_buffer, formatted_output);
            fprintf(fout, "%s\t", formatted_output);
        }
    }

    if (!endd) {
        char deformatted[MAX_STRING_LENGTH];
        fprintf(fout, "\n\nMonitors:\n");

        /* Monitor 1 - PC */
        if ((strcmp(EXMEM.opcode, "beq") == 0 && EXMEM.zero && EXMEM.branch && 0) ||
            (strcmp(EXMEM.opcode, "bne") == 0 && !EXMEM.zero && EXMEM.branch && 0)) {
            intToHex(EXMEM.target * 4, hex_buffer);
            trim(hex_buffer, formatted_output);
            fprintf(fout, "%s\t", formatted_output);
        } else {
            intToHex((PC) * 4, hex_buffer);
            trim(hex_buffer, formatted_output);
            fprintf(fout, "%s\t", formatted_output);
        }

        /* Monitor 2 - Instruction */
        if ((strcmp(EXMEM.opcode, "beq") == 0 && EXMEM.zero && EXMEM.branch && 0) ||
            (strcmp(EXMEM.opcode, "bne") == 0 && !EXMEM.zero && EXMEM.branch && 0)) {
            intToHex(IDEX.PC1 * 4, hex_buffer);
            trim(hex_buffer, formatted_output);
            fprintf(fout, "%s\t", formatted_output);
        } else {
            intToHex((PC * 4 - 4), hex_buffer);
            trim(hex_buffer, formatted_output);
            fprintf(fout, "%s\t", formatted_output);
        }

        /* Monitor 3 - Deformatted instruction */
        deformater(IFID.instr, IFID.opcode, deformatted);
        fprintf(fout, "%s\t", deformatted);

        /* Monitor 4 - Label */
        fprintf(fout, "%s\t", EXMEM.string_lbl);

        /* Monitor 5-28 */
        fprintf(fout, "$%s\t", mipsRegisters[IDEX.rs]);
        fprintf(fout, "$%s\t", mipsRegisters[IDEX.rt]);
        fprintf(fout, "$%s\t", mipsRegisters[MEMWB.wr]);

        intToHex(MEMWB.write_data, hex_buffer);
        trim(hex_buffer, formatted_output);
        fprintf(fout, "%s\t", formatted_output);

        intToHex(IDEX.readA, hex_buffer);
        trim(hex_buffer, formatted_output);
        fprintf(fout, "%s\t", formatted_output);

        intToHex(IDEX.readB, hex_buffer);
        trim(hex_buffer, formatted_output);
        fprintf(fout, "%s\t", formatted_output);

        intToHex(IDEX.immed, hex_buffer);
        trim(hex_buffer, formatted_output);
        fprintf(fout, "%s\t", formatted_output);

        fprintf(fout, "$%s\t", mipsRegisters[IDEX.rs]);
        fprintf(fout, "$%s\t", mipsRegisters[IDEX.rt]);
        fprintf(fout, "$%s\t", mipsRegisters[IDEX.rt]);
        fprintf(fout, "$%s\t", mipsRegisters[IDEX.rd]);

        intToHex(IDEX.readA, hex_buffer);
        trim(hex_buffer, formatted_output);
        fprintf(fout, "%s\t", formatted_output);

        if (!EXMEM.ALUsrc) {
            intToHex(EXMEM.readB, hex_buffer);
            trim(hex_buffer, formatted_output);
            fprintf(fout, "%s\t", formatted_output);
        } else {
            intToHex(EXMEM.immed, hex_buffer);
            trim(hex_buffer, formatted_output);
            fprintf(fout, "%s\t", formatted_output);
        }

        intToHex(EXMEM.aluout, hex_buffer);
        trim(hex_buffer, formatted_output);
        fprintf(fout, "%s\t", formatted_output);

        intToHex(EXMEM.readB, hex_buffer);
        trim(hex_buffer, formatted_output);
        fprintf(fout, "%s\t", formatted_output);

        intToHex(MEMWB.aluout, hex_buffer);
        trim(hex_buffer, formatted_output);
        fprintf(fout, "%s\t", formatted_output);

        intToHex(MEMWB.mem_in, hex_buffer);
        trim(hex_buffer, formatted_output);
        fprintf(fout, "%s\t", formatted_output);

        intToHex(MEMWB.mem_out, hex_buffer);
        trim(hex_buffer, formatted_output);
        fprintf(fout, "%s\t", formatted_output);

        intToHex(MEMWB.aluout, hex_buffer);
        trim(hex_buffer, formatted_output);
        fprintf(fout, "%s\t", formatted_output);

        fprintf(fout, "$%s\t", mipsRegisters[MEMWB.wr]);
        fprintf(fout, "$%s\t", mipsRegisters[MEMWB.wr]);

        if (MEMWB.memtoreg) {
            intToHex(MEMWB.mem_out, hex_buffer);
            trim(hex_buffer, formatted_output);
            fprintf(fout, "%s\t", formatted_output);
        } else {
            intToHex(MEMWB.aluout, hex_buffer);
            trim(hex_buffer, formatted_output);
            fprintf(fout, "%s\t", formatted_output);
        }

        fprintf(fout, "%d\t", hazard);
        fprintf(fout, "%d\t", forwarding);
    }

    fprintf(fout, "\n\nMemory State:\n");


        for (int i = 0; i < mmp; i++) {
            if (memAddress[i] != 0) {
                intToHex(MEM[i], hex_buffer);
                trim(hex_buffer, formatted_output);
                fprintf(fout, "%s\t", formatted_output);
            }
        }


    fprintf(fout, "\n");

    if (!endd) {
        char deformatted1[MAX_STRING_LENGTH], deformatted2[MAX_STRING_LENGTH];
        char deformatted3[MAX_STRING_LENGTH], deformatted4[MAX_STRING_LENGTH];

        fprintf(fout, "\nPipeline Stages:\n");

        deformater(IFID.instr, IFID.opcode, deformatted1);
        deformater(IDEX.instr, IDEX.opcode, deformatted2);
        deformater(EXMEM.instr, EXMEM.opcode, deformatted3);
        deformater(MEMWB.instr, MEMWB.opcode, deformatted4);

        fprintf(fout, "%s\t%s\t%s\t%s\t", deformatted1, deformatted2, deformatted3, deformatted4);
    }

    if (endd) {
        fprintf(fout, "\nTotal Cycles:\n%d", cycles - 1);
        fprintf(fout, "\n\nTotal Execution Time: \n%f (ns)", userTime * 1000000000);
    }

    fclose(fout);
}

void monitors() {
    /* Debug print to see current cycle and requested cycles */
    printf("Current cycle: %d, Checking against: %d\n", cycles, cyc_to_print[cyc_count]);

    if (cyc_to_print[cyc_count] == 0) {
        /* If set to 0, print every cycle */
        print_monitors(0);
    } else if (cycles == cyc_to_print[cyc_count]) {
        /* Print specific requested cycles */
        print_monitors(0);
        cyc_count++;  /* Move to next cycle in the array */
    }
}

void init_out() {
    FILE* fout;
    fout = fopen("output.txt", "w");
    if (!fout) {
        exit(-4);
    }
    fprintf(fout, "Name: Giorgos Tsiapalis\nID: UC1066232\n");
    fclose(fout);
}

void IFflush(int fl) {
    if (fl) {
        IFID.ALUsrcA = 0;
        IFID.ALUsrcB = 0;
        IFID.immed = 0;
        strcpy(IFID.instr, "sll$zero,$zero,0");
        IFID.memread = 0;
        IFID.memwrite = 0;
        strcpy(IFID.opcode, "sll");
        IFID.rd = 0;
        IFID.rs = 0;
        IFID.rt = 0;
        IFID.regwrite = 0;
        strcpy(IFID.string_lbl, "-");
        IFID.branch = 0;
        IFID.target = 0;
        strcpy(IFID.type, "I");
        IFID.wr = 0;
        ifflush = 0;
    }
}

void bubbles() {
    IFID.memwrite = 0;
    IFID.regwrite = 0;
    IFID.branch = 0;

    IDEX.memwrite = 0;
    IDEX.regwrite = 0;
    IDEX.branch = 0;
}

void hazardDetectionAndForwarding() {
    IDEX.ALUsrcA = 0;
    IDEX.ALUsrcB = 0;
    hazard = 0;
    forwarding = 0;

    if (MEMWB.wr == IDEX.rs && MEMWB.wr != 0) {
        forwarding = 1;
        if (MEMWB.regwrite) {
            IDEX.ALUsrcA = 2;
            MEMWB.fw = MEMWB.aluout;
            if (strcmp(MEMWB.opcode, "lw") == 0) {
                MEMWB.fw = MEMWB.mem_out;
            }
            hazard = 1;
        }
    }

    if (MEMWB.wr == IDEX.rt && MEMWB.wr != 0) {
        forwarding = 1;
        if (MEMWB.regwrite) {
            IDEX.ALUsrcB = 2;
            MEMWB.fw = MEMWB.aluout;
            if (strcmp(MEMWB.opcode, "lw") == 0) {
                MEMWB.fw = MEMWB.mem_out;
            }
            hazard = 1;
        }
    }

    if (EXMEM.wr == IDEX.rs && EXMEM.wr != 0) { /* Priority to EX hazard */
        forwarding = 1;
        if (EXMEM.regwrite) {
            IDEX.ALUsrcA = 1;
            hazard = 1;
        }
    }

    if (EXMEM.wr == IDEX.rt && EXMEM.wr != 0 && EXMEM.regwrite) { /* Priority to EX hazard */
        forwarding = 1;
        if (EXMEM.regwrite) {
            IDEX.ALUsrcB = 1;
            hazard = 1;
        }
    }

    /* LOAD USE CHECK */
    if (strcmp(IDEX.opcode, "lw") == 0 && (IDEX.wr == IFID.rs || IDEX.wr == IFID.rt)) {
        PC--;
        nextPC--;
        IFflush(1);
        hazard = 1;
    }

    /* CONTROL HAZARDS */
    if (strcmp(IFID.opcode, "beq") == 0 && reg[IFID.rs] == reg[IFID.rt]) {
        PC = IFID.target - 1;
        IFID.branch = 0;
        ifflush = 1;
        hazard = 1;
    }

    if (strcmp(IFID.opcode, "bne") == 0 && reg[IFID.rs] != reg[IFID.rt]) {
        PC = IFID.target - 1; /* And not the next PC */
        IFID.branch = 0;
        ifflush = 1;
        hazard = 1;
    }
}

void brnch() {
    if (IDEX.branch && IDEX.zero && strcmp(IDEX.opcode, "beq") == 0) {
        PC = IDEX.target - 1;
    }
    if (IDEX.branch && !IDEX.zero && strcmp(IDEX.opcode, "bne") == 0) {
        PC = IDEX.target - 1;
    }
}

void update() {
    strcpy(opcode, MEMWB.opcode);
    strcpy(instr_evicted, MEMWB.instr);

    /* Update MEMWB from EXMEM */
    MEMWB.rs = EXMEM.rs;
    MEMWB.rt = EXMEM.rt;
    MEMWB.rd = EXMEM.rd;
    MEMWB.wr = EXMEM.wr;
    MEMWB.target = EXMEM.target;
    MEMWB.PC1 = EXMEM.PC1;
    strcpy(MEMWB.instr, EXMEM.instr);
    MEMWB.readA = EXMEM.readA;
    MEMWB.readB = EXMEM.readB;
    MEMWB.regdst = EXMEM.regdst;
    MEMWB.branch = EXMEM.branch;
    MEMWB.memread = EXMEM.memread;
    MEMWB.memwrite = EXMEM.memwrite;
    MEMWB.memtoreg = EXMEM.memtoreg;
    MEMWB.regwrite = EXMEM.regwrite;
    MEMWB.ALUsrc = EXMEM.ALUsrc;
    MEMWB.ALUsrcA = EXMEM.ALUsrcA;
    MEMWB.ALUsrcB = EXMEM.ALUsrcB;
    MEMWB.immed = EXMEM.immed;
    MEMWB.aluop = EXMEM.aluop;
    MEMWB.aluout = EXMEM.aluout;
    MEMWB.mem_in = EXMEM.mem_in;
    MEMWB.mem_out = EXMEM.mem_out;
    MEMWB.write_data = EXMEM.write_data;
    MEMWB.zero = EXMEM.zero;
    strcpy(MEMWB.opcode, EXMEM.opcode);
    strcpy(MEMWB.type, EXMEM.type);
    strcpy(MEMWB.string_lbl, EXMEM.string_lbl);

    /* Update EXMEM from IDEX */
    EXMEM.rs = IDEX.rs;
    EXMEM.rt = IDEX.rt;
    EXMEM.rd = IDEX.rd;
    EXMEM.wr = IDEX.wr;
    EXMEM.target = IDEX.target;
    EXMEM.PC1 = IDEX.PC1;
    strcpy(EXMEM.instr, IDEX.instr);
    EXMEM.readA = IDEX.readA;
    EXMEM.readB = IDEX.readB;
    EXMEM.regdst = IDEX.regdst;
    EXMEM.branch = IDEX.branch;
    EXMEM.memread = IDEX.memread;
    EXMEM.memwrite = IDEX.memwrite;
    EXMEM.memtoreg = IDEX.memtoreg;
    EXMEM.regwrite = IDEX.regwrite;
    EXMEM.ALUsrc = IDEX.ALUsrc;
    EXMEM.ALUsrcA = IDEX.ALUsrcA;
    EXMEM.ALUsrcB = IDEX.ALUsrcB;
    EXMEM.immed = IDEX.immed;
    EXMEM.aluop = IDEX.aluop;
    EXMEM.aluout = IDEX.aluout;
    EXMEM.mem_in = IDEX.mem_in;
    EXMEM.mem_out = IDEX.mem_out;
    EXMEM.write_data = IDEX.write_data;
    EXMEM.zero = IDEX.zero;
    strcpy(EXMEM.opcode, IDEX.opcode);
    strcpy(EXMEM.type, IDEX.type);
    strcpy(EXMEM.string_lbl, IDEX.string_lbl);

    /* Update IDEX from IFID */
    IDEX.rs = IFID.rs;
    IDEX.rt = IFID.rt;
    IDEX.rd = IFID.rd;
    IDEX.wr = IFID.wr;
    IDEX.target = IFID.target;
    IDEX.PC1 = IFID.PC1;
    strcpy(IDEX.instr, IFID.instr);
    IDEX.readA = IFID.readA;
    IDEX.readB = IFID.readB;
    IDEX.regdst = IFID.regdst;
    IDEX.branch = IFID.branch;
    IDEX.memread = IFID.memread;
    IDEX.memwrite = IFID.memwrite;
    IDEX.memtoreg = IFID.memtoreg;
    IDEX.regwrite = IFID.regwrite;
    IDEX.ALUsrc = IFID.ALUsrc;
    IDEX.ALUsrcA = IFID.ALUsrcA;
    IDEX.ALUsrcB = IFID.ALUsrcB;
    IDEX.immed = IFID.immed;
    IDEX.aluop = IFID.aluop;
    IDEX.aluout = IFID.aluout;
    IDEX.mem_in = IFID.mem_in;
    IDEX.mem_out = IFID.mem_out;
    IDEX.write_data = IFID.write_data;
    IDEX.zero = IFID.zero;
    strcpy(IDEX.opcode, IFID.opcode);
    strcpy(IDEX.type, IFID.type);
    strcpy(IDEX.string_lbl, IFID.string_lbl);
}

int main(int argc, char *argv[]) {
    int i = 0;

    // Initialize arrays to prevent undefined behavior
    memset(cyc_to_print, 0, sizeof(cyc_to_print));
    memset(memAddress, 0, sizeof(memAddress));
    memset(MEM, 0, sizeof(MEM));

    // Initialize label arrays
    for (int j = 0; j < lbl_max; j++) {
        label_nm[j][0] = '\0';
        LBL[j] = 0;
    }

    printf("Command file name: ");
    scanf("%s", file_name);
    printf("Cycles to print in ascending order (-1 to continue, 0 for all): \n");
    do {
        scanf("%d", &cyc_to_print[i]);
        i++;
        // Prevent buffer overflow
        if (i >= 99) break;
    } while (cyc_to_print[i-1] != -1 && cyc_to_print[i-1] != 0);

    preparser();
    init_out();
    fillMem();
    mainline = starter() + 1;

    start_time = clock();

    // Add a maximum cycle count to prevent infinite loop
    int max_cycles = 10000;
    while (cycles < max_cycles) {
        nextPC = mainline + PC;

        IFflush(ifflush);
        reg_file();
        memory();
        hazardDetectionAndForwarding();
        ALU();
        reg_file();
        control_unit();
        update();
        instr_reg(nextPC);
        monitors();
        cycles++;

        // Debug print
        if (cycles % 100 == 0) {
            printf("Completed %d cycles\n", cycles);
        }
    }

    printf("Maximum cycle count reached. Exiting.\n");
    print_monitors(1);
    return 0;
}

/* 0 ALL GOOD - 1 NO FILE - 2 INVALID COMMAND - 3 OUT OF MEMORY - 4 OUT FILE ERROR - 5 PREPARSER ERROR - 6 OUT OF LABEL SPACE */