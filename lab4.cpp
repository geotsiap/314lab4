//shift implementes as I type

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

#include<iostream>
#include <fstream>
#include<string>
#include <sstream>
#include <iomanip>
#include<cmath>
#include<bitset>
#include <ctime>

#define mmp 256      //max memory positions
#define lbl_max 256  //max label positions

using namespace std;

void print_monitors(bool endd);
int lbl_trans(string label);

string mipsRegisters[33] = {
        "zero", "at", "v0", "v1", "a0", "a1", "a2", "a3",
        "t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7",
        "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7",
        "t8", "t9", "k0", "k1", "gp", "sp", "fp", "ra", "-"};

int reg[33];

struct pipeline{
    int rs;
    int rt;
    int rd;
    int wr;
    int target;
    int PC1;
    string instr;
    int readA;
    int readB;
    bool regdst;
    bool branch;
    bool memread;
    bool memwrite;
    bool memtoreg;
    bool regwrite;
    int ALUsrc;
    int ALUsrcA=0;
    int ALUsrcB=0;
    int fw;
    int immed;
    int aluop;
    int aluout;
    int mem_in;
    int mem_out;
    int write_data;
    bool zero;
    string string_lbl="-";
    string opcode;
    string type;
};
pipeline IFID, IDEX, EXMEM, MEMWB, EXT;

long memAddress[mmp];
long MEM[mmp];

string label_nm[lbl_max];
int LBL[lbl_max];
int label_count=0;

clock_t start_time, end_time;
double userTime;

int PC=0, nextPC;
int mainline;
bool EOF_flag=0;
bool ifflush=0;
bool stall=false;
bool hazard, forwarding;

int cyc_to_print[100];
int cyc_count=0;

//control signals
bool regdst, jump, branch, memread, memtoreg, memwrite, ALUsrc, regwrite, zero;
int aluop;

//monitors
int /*PC, rs, rt*/ wr, write_data, readA, readB, aluout, target, mem_in, mem_out;
string instr, opcode, type, instr_evicted/*R I J SPI B*/;

string file_name;
int rs, rt, rd, address, immed, cycles=1;

int hex_dec(string hexString) {
    int decimalValue;
    istringstream(hexString) >> hex >> decimalValue;
    return decimalValue;
}

string intToHex(int value) {
    stringstream stream;

    // Ensure the value fits within 32 bits (4 bytes)
    value &= 0xFFFFFFFF;

    // Convert to hexadecimal
    stream << hex << uppercase << setw(8) << setfill('0') << value;

    return stream.str();
}

string intToBinary(unsigned int num) {
    // Ensure the input number is within the range [0, 15]
    num = num & 0xF;

    // Convert the integer to its binary representation
    bitset<4> binary(num);

    // Convert the binary representation to a string
    return binary.to_string();
}

string trim(string in){
    int l=in.length();
    bool found=0;
    string out="";

    for(int i=0; i<l; i++){
        if(in[i]=='0' && !found){
            continue;
        }else{
            if(in[i]!='0' || found){
                found=1;
                out+=in[i];
            }
        }
    }

    if(out=="")
        out="0";

    return out;
}

int stringToInt(const string& str) {
    try {
        return stoi(str);
    } catch (const invalid_argument& e) {
        cout<<str;
        cerr << "Invalid argument: " << e.what() << endl;
        return 0;
    } catch (const out_of_range& e) {
        cout<<str;
        cerr << "Out of range: " << e.what() << endl;
        return 0;
    }
}

unsigned int directToInt(string hex) {
    unsigned int sum=0;

    for(int i=0; i<8; i++){
        switch(hex[i]){
            case 'F':
                sum+=pow(2, (((8-i)*4)-1));
                sum+=pow(2, (((8-i)*4)-2));
                sum+=pow(2, (((8-i)*4)-3));
                sum+=pow(2, (((8-i)*4)-4));
            break;

            case 'E':
                sum+=pow(2, (((8-i)*4)-1));
                sum+=pow(2, (((8-i)*4)-2));
                sum+=pow(2, (((8-i)*4)-3));
            break;

            case 'D':
                sum+=pow(2, (((8-i)*4)-1));
                sum+=pow(2, (((8-i)*4)-2));
                sum+=pow(2, (((8-i)*4)-4));
            break;

            case 'C':
                sum+=pow(2, (((8-i)*4)-1));
                sum+=pow(2, (((8-i)*4)-2));
            break;

            case 'B':
                sum+=pow(2, (((8-i)*4)-1));
                sum+=pow(2, (((8-i)*4)-3));
                sum+=pow(2, (((8-i)*4)-4));
            break;

            case 'A':
                sum+=pow(2, (((8-i)*4)-1));
                sum+=pow(2, (((8-i)*4)-3));
            break;

            case '9':
                sum+=pow(2, (((8-i)*4)-1));
                sum+=pow(2, (((8-i)*4)-4));
            break;

            case '8':
                sum+=pow(2, (((8-i)*4)-1));
            break;

            case '7':
                sum+=pow(2, (((8-i)*4)-2));
                sum+=pow(2, (((8-i)*4)-3));
                sum+=pow(2, (((8-i)*4)-4));
            break;

            case '6':
                sum+=pow(2, (((8-i)*4)-2));
                sum+=pow(2, (((8-i)*4)-3));
            break;

            case '5':
                sum+=pow(2, (((8-i)*4)-2));
                sum+=pow(2, (((8-i)*4)-4));
            break;

            case '4':
                sum+=pow(2, (((8-i)*4)-2));
            break;

            case '3':
                sum+=pow(2, (((8-i)*4)-3));
                sum+=pow(2, (((8-i)*4)-4));
            break;

            case '2':
                sum+=pow(2, (((8-i)*4)-3));
            break;

            case '1':
                sum+=pow(2, (((8-i)*4)-4));
            break;
        }
    }

    return sum;
}

string parser(int line){
    ifstream fl;
    string com="";

    EOF_flag=false;
    fl.open(file_name);
	if (!fl.is_open()) {
		exit(-1);
	}
	//FILE OK

    int j=1;
	while (j<=line) {
        if (!getline(fl, com)) {
            EOF_flag=true;
            break; // Reached the end of the file
        }
        j++;
    }

    fl.close();
    return com;
}

string formater(string inp){ //removes tabs, new lines, and spaces
	int len=inp.length();
	string out="";

	for(int i=0; i<len; i++){
		if(inp[i]=='#'){
			break;
		}else{
			if(inp[i]!=' ' && inp[i]!='\t' && inp[i]!='\n'){
				out+=inp[i];
			}
		}
	}

    //cout<<endl<<out;
	return out;
}

string deformater(string in, string inop){
    string out="";

    if(in[0]=='j'){
        out+='j';
        out+=' ';
        for(int i=1; i<in.length(); i++){
            out+=in[i];
        }
        return out;
    }

    //cout<<inop<<endl;

    if(inop=="add" || inop=="addu"  || inop=="and" || inop=="nor" || inop=="or" || inop=="slt" || inop=="sltu" || inop=="sub" || inop=="subu"){ //R-TYPE
        for(int i=0; i<in.length(); i++){
            out+=in[i];
            if(in[i+1]=='$'){
                out+=' ';
            }
        }
        return out;
    }

    if(inop=="addi" || inop=="addui" || inop=="addiu" || inop=="andi" || inop=="ori" || inop=="slti" || inop=="sltiu" || inop=="sltui" || inop=="sll" || inop=="srl" || inop=="beq" || inop=="bne"){ //I/B-TYPE
        int comma=0, dol=0;
        for(int i=0; i<in.length(); i++){
            out+=in[i];
            if(in[i+1]=='$'){
                out+=' ';
                dol++;
            }
            if(in[i]==','){
                comma++;
                if(comma==2){
                    out+=' ';
                }
            }
        }
        return out;
    }

    if(inop=="lw" || IFID.opcode=="sw"){ //SPECIAL-I-TYPE
        int i=0;
        while(in[i+1]!='$'){
            out+=in[i];
            i++;
        }
        out+=in[i];
        i++;
        out+=' ';
        while(in[i]!=','){
            out+=in[i];
            i++;
        }
        out+=in[i];//comma
        i++;
        out+=' ';
        while(i<in.length()){
            out+=in[i];
            i++;
        }
        return out;
    }

    //exit(-7);
    return "";
}

int starter(){ //finds the line where main starts
	int line=0;
	string com;
	string temp;

	while(1){
		com=parser(line);
		temp="";

		if(com.length() >= 5){
			for(int i=0; i<5; i++){
				temp+=com[i];
			}
			if(temp=="main:"){
				return line++;
			}
		}

		line++;
	}
}

void submit_label(string name, int pointer){
    if(label_count==lbl_max){
        exit(-6);
    }

    label_nm[label_count]=name;
    LBL[label_count]=pointer;
    label_count++;
}

void preparser(){
    ofstream fout;
    fout.open("instr.txt");
    int i=0, stalls=0;
    string line;
    bool isLabel;
    int empt=0;

    if (!fout.is_open()) {
		exit(-5);
	}

    mainline=starter();
    for(i=0; i<=mainline; i++){
        fout<<parser(i)<<endl;
    }

    do{
        isLabel=false;
        line=formater(parser(i));
        if(line!=""){
            if(line[line.length()-1]==':'){
                string lbl_bd="";
                int lbl_ln=i-empt-mainline-1-label_count;//=========TO BE REMOVED
                for(int j=0; j<line.length()-1; j++){
                    lbl_bd+=line[j];
                }
                submit_label(lbl_bd, lbl_ln);
            }else{
                fout<<line<<endl;
            }
        }else{
            empt++;
        }
        i++;
    }while(!EOF_flag);
    //fout<<"sll$zero,$zero,0"<<endl;
    fout<<"sll$zero,$zero,0"<<endl;
    fout<<"sll$zero,$zero,1"<<endl;
    fout<<"sll$zero,$zero,0";

    file_name="instr.txt";
    fout.close();
}

int reg_trans(string alias) { //register translation from alias to number
    for (int i = 0; i < 32; i++) {
        if (mipsRegisters[i] == alias) {
            return i;
        }
    }
    return -1; // Return -1 if the alias is not found
}

void j_type(string com){    //NOT USED
	string address_str="";
	string rs_str="";
    string label_str="";
    IFID.type="J";

	switch(com[1]){

		case 'a': //jal
			for(int i=3; i<com.length(); i++){
				address_str+=com[i];
			}
			reg[reg_trans("ra")]=PC; //save $ra
			opcode="jal";
		break;

		case 'r': //jr$
			for(int i=3; i<com.length(); i++){
				rs_str+=com[i];
			}
			address_str=intToHex(reg[reg_trans(rs_str)]);
			opcode="jr";
		break;

		default://j
			for(int i=1; i<com.length(); i++){
				label_str+=com[i];
			}
			opcode="j";
		break;
	}

	//rs=reg_trans(rs_str); ENABLE IF JRRRRRRRRRRRRRRRRRRR
	address=LBL[lbl_trans(label_str)];
	IFID.rs=32;
	IFID.rt=32;
	IFID.rd=32;
}

void r_type(string com){
	int i;
	string rs_str="";
	string rt_str="";
	string rd_str="";
	IFID.type="R";
	IFID.string_lbl="-";

	i=0;
	do{
		i++;
	}while(com[i]!='$');
	//opcode done
	i++;
	//rd start
	do{
		rd_str+=com[i];
		i++;
	}while(com[i]!=',');
	//rd done
	i++;
	i++;
	//rs start
	do{
		rs_str+=com[i];
		i++;
	}while(com[i]!=',');
	//rs done
	i++;
	i++;
	//rt start
	do{
		rt_str+=com[i];
		i++;
	}while(i<com.length());

	IFID.rs=reg_trans(rs_str);
	IFID.rt=reg_trans(rt_str);
	IFID.rd=reg_trans(rd_str);
	IFID.wr=reg_trans(rd_str);
}

void b_type(string com){
    int i;
	string rs_str="";
	string rt_str="";
	string label_str="";
	IFID.type="B";

	i=0;
	do{
		i++;
	}while(com[i]!='$');
	//opcode done
	i++;
	//rt start
	do{
		rt_str+=com[i];
		i++;
	}while(com[i]!=',');
	//rt done
	i++;
	i++;
	//rs start
	do{
		rs_str+=com[i];
		i++;
	}while(com[i]!=',');
	//rs done
	i++;
	//label start
	do{
		label_str+=com[i];
		i++;
	}while(i<com.length());

	IFID.rs=reg_trans(rs_str);
	IFID.rt=reg_trans(rt_str);
	IFID.wr=0;
	IFID.target=LBL[lbl_trans(label_str)];
	IFID.string_lbl=label_str;
	//cout<<endl<<target<<endl;
	IFID.rd=32;
}

void i_type(string com){
    int i;
	string rs_str="";
	string rt_str="";
	string immed_str="";
	IFID.type="I";
	IFID.string_lbl="-";

	i=0;
	do{
		i++;
	}while(com[i]!='$');
	//opcode done
	i++;
	//rt start
	do{
		rt_str+=com[i];
		i++;
	}while(com[i]!=',');
	//rt done
	i++;
	i++;
	//rs start
	do{
		rs_str+=com[i];
		i++;
	}while(com[i]!=',');
	//rs done
	i++;
	//immed start
	do{
		immed_str+=com[i];
		i++;
	}while(i<com.length());

	IFID.rs=reg_trans(rs_str);
	IFID.rt=reg_trans(rt_str);
	IFID.wr=reg_trans(rt_str);
	if(immed_str[0]=='0' && immed_str[1]=='x'){
        string temp="";
        for(int j=2; j<=immed_str.length(); j++){
            temp+=immed_str[j];
        }
        IFID.immed=hex_dec(temp);
	}else{
        IFID.immed=stringToInt(immed_str);
	}
	IFID.rd=32;
}

void special_i_type(string com){
    int i;
	string rs_str="";
	string rt_str="";
	string immed_str="";
	IFID.type="SPI";
	IFID.string_lbl="-";

	i=0;
	do{
		i++;
	}while(com[i]!='$');
	//opcode done
	i++;
	//rt start
	do{
		rt_str+=com[i];
		i++;
	}while(com[i]!=',');
	//rt done
	i++;//skip comma


	while(com[i]>='0' && com[i]<='9'){
        immed_str+=com[i];
        i++;
	}
	//cout<<immed_str<<endl;
	//immed done
	i++;//skip parentheses
	i++;//skip $
	//rs start
	do{
		rs_str+=com[i];
		i++;
	}while(com[i]!=')');

	if(rs_str=="pc"){
        IFID.rs=PC+1;
	}else{
        IFID.rs=reg_trans(rs_str);
	}
	IFID.rt=reg_trans(rt_str);
	IFID.immed=stringToInt(immed_str);
	IFID.wr=reg_trans(rt_str);
	IFID.rd=32;
}

void instr_reg(int line){
	string com=formater(parser(line));
	instr=com;
	IFID.instr=com;
	string opcd="";
	int i=0;

	PC++;
    IFID.PC1=PC;

	cout<<com<<endl;

	if(com[0]=='j'){ //J-TYPE
		j_type(com);
	}else{
		i=0;
		do{
			opcd+=com[i];
			i++;
		}while(com[i]!='$');
		IFID.opcode=opcd;
		//exo to opcode se string;

		if(opcd=="add" || opcd=="addu"  || opcd=="and" || opcd=="nor" || opcd=="or" || opcd=="slt" || opcd=="sltu" || opcd=="sub" || opcd=="subu"){ //R-TYPE
			r_type(com);
		}else{
			if(opcd=="addi" || opcd=="addui" || opcd=="addiu" || opcd=="andi" || opcd=="ori" || opcd=="slti" || opcd=="sltiu" || opcd=="sltui" || opcd=="sll" || opcd=="srl"){ //I-TYPE
				i_type(com);
			}else{
			    if(opcd=="sw" || opcd=="lw"){ //SPECIAL-I-TYPE
                    special_i_type(com);
                }else{
                    if(opcd=="beq" || opcd=="bne"){ //B-TYPE
                        b_type(com);
                    }else{
                        exit(-2);
                    }
                }
			}
		}
	}
	//theoritika exo opcode, rs, rt, rd, func, immed, address
}

int target_calc(){ //also monitor 10
	//target=PC+immed;//not *4 bcs addresses go +1
	return target;
}

void control_unit(){

    //PC++;

    if(IFID.instr=="sll$zero,$zero,1"){
        end_time=clock();
        userTime=static_cast<double>(end_time-start_time)/CLOCKS_PER_SEC;
        print_monitors(true);
		exit(0);
	}

	if(IFID.opcode=="add"){
		IFID.regdst=1;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=2;//add
		IFID.memwrite=0;
		IFID.ALUsrc=0;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="addi"){
		IFID.regdst=0;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=2;//add
		IFID.memwrite=0;
		IFID.ALUsrc=1;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="addui" || IFID.opcode=="addiu"){
		IFID.regdst=0;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=7;//addu
		IFID.memwrite=0;
		IFID.ALUsrc=1;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="addu"){
		IFID.regdst=1;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=7;//addu
		IFID.memwrite=0;
		IFID.ALUsrc=0;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="and"){
		IFID.regdst=1;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=0;//and
		IFID.memwrite=0;
		IFID.ALUsrc=0;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="andi"){
		IFID.regdst=0;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=0;//and
		IFID.memwrite=0;
		IFID.ALUsrc=1;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="beq"){
		IFID.regdst=0;
		IFID.branch=1;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=6;//sub
		IFID.memwrite=0;
		IFID.ALUsrc=0;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=0;
	}

	if(IFID.opcode=="bne"){
		IFID.regdst=0;
		IFID.branch=1;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=6;//sub
		IFID.memwrite=0;
		IFID.ALUsrc=0;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=0;
	}

	if(IFID.opcode=="lw"){
		IFID.regdst=0;
		IFID.branch=0;
		IFID.memread=1;
		IFID.memtoreg=1;
		IFID.aluop=2;//add
		IFID.memwrite=0;
		IFID.ALUsrc=1;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="nor"){
		IFID.regdst=1;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=12;//nor
		IFID.memwrite=0;
		IFID.ALUsrc=0;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="or"){
		IFID.regdst=1;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=1;//or
		IFID.memwrite=0;
		IFID.ALUsrc=0;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="ori"){
		IFID.regdst=0;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=1;//or
		IFID.memwrite=0;
		IFID.ALUsrc=1;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="slt"){
		IFID.regdst=1;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=3;//slt
		IFID.memwrite=0;
		IFID.ALUsrc=0;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="slti"){
		IFID.regdst=0;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=3;//slt
		IFID.memwrite=0;
		IFID.ALUsrc=1;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="sltiu" || opcode=="sltui"){
		IFID.regdst=0;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=8;//sltu
		IFID.memwrite=0;
		IFID.ALUsrc=1;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="sltu"){
		IFID.regdst=1;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=8;//sltu
		IFID.memwrite=0;
		IFID.ALUsrc=0;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="sll"){
		IFID.regdst=0;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=5;//sll
		IFID.memwrite=0;
		IFID.ALUsrc=1;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="srl"){
		IFID.regdst=0;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=4;//srl
		IFID.memwrite=0;
		IFID.ALUsrc=1;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="sw"){
		IFID.regdst=0;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=1;
		IFID.aluop=2;//add
		IFID.memwrite=1;
		IFID.ALUsrc=1;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=0;
	}

	if(IFID.opcode=="sub"){
		IFID.regdst=1;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=6;//sub
		IFID.memwrite=0;
		IFID.ALUsrc=0;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="subu"){
		IFID.regdst=1;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=9;//subu
		IFID.ALUsrc=0;
		IFID.ALUsrc=0;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=1;
	}

	if(IFID.opcode=="j" || IFID.opcode=="jal"){
		IFID.regdst=0;
		IFID.branch=0;
		IFID.memread=0;
		IFID.memtoreg=0;
		IFID.aluop=2;//add
		IFID.memwrite=0;
		IFID.ALUsrc=0;
		IFID.ALUsrcA=0;
		IFID.ALUsrcB=0;
		IFID.regwrite=0;
	}
}

void reg_file(){


	if(MEMWB.memtoreg){
		MEMWB.write_data=MEMWB.mem_out;
	}else{
		MEMWB.write_data=MEMWB.aluout;
	}
	//cout<<MEMWB.mem_out<<"  "<<MEMWB.aluout<<"   "<<MEMWB.write_data<<"  ";

	if(MEMWB.regdst){
		MEMWB.wr=MEMWB.rd;//write register
	}else{
		MEMWB.wr=MEMWB.rt;
	}
	//cout<<mipsRegisters[MEMWB.wr]<<"  "<<MEMWB.regwrite;

	if(MEMWB.regwrite){
		reg[MEMWB.wr]=MEMWB.write_data;
	}

    IFID.readA=reg[IFID.rs];
	//cout<<mipsRegisters[IFID.rs]<<"  "<<IFID.readA<<endl;
	IFID.readB=reg[IFID.rt];
	IFID.mem_in=IFID.readB;//epidi to ALU tha pari immed san inB MPORI NA PREPI NA ALLKSI============================================

}

void ALU(){
	int inA=IDEX.readA;
	int inB;
	//cout<<IDEX.ALUsrcA<<"  "<<IDEX.ALUsrcB<<" ";


	switch (IDEX.ALUsrcA){
        case 0:
            inA=IDEX.readA;
        break;

        case 1:
            inA=EXMEM.aluout;
        break;

        case 2:
            inA=MEMWB.fw;
        break;
	}

	switch (IDEX.ALUsrcB){
        case 0:
            inB=IDEX.readB;
        break;

        case 1:
            inB=EXMEM.aluout;
        break;

        case 2:
            inB=MEMWB.fw;
        break;
	}


    if(IDEX.ALUsrc){
        inB=IDEX.immed;
    }

    //cout<<mipsRegisters[IDEX.rs]<<inA<<"  "<<inB<<"  "<<IDEX.ALUsrc<<"  "<<IDEX.aluop<<"  ";

	switch(IDEX.aluop){

		case 2://add
			aluout=inA+inB;
		break;

		case 6://sub
			aluout=inA-inB;
		break;

		case 3://slt
			aluout=inA-inB;
			if(aluout<0)
                aluout=1;
            else
                aluout=0;
		break;

		case 8://sltu
			aluout=directToInt(intToHex(inA))-directToInt(intToHex(inB));
			if(aluout<0)
                aluout=1;
            else
                aluout=0;
		break;

		case 0://and
			aluout=inA & inB;
		break;

		case 1://or
			aluout=inA | inB;
		break;

		case 12://nor
			aluout=~(inA | inB);
		break;

		case 5://sll
			aluout=inA;
			for(int i=0; i<inB; i++){
				aluout*=2;
			}
		break;

		case 4://srl
			aluout=inA;
			for(int i=0; i<inB; i++){
				aluout/=(int)2;
			}
		break;

		case 7://addu
            aluout=directToInt(intToHex(inA))+directToInt(intToHex(inB));
        break;

        case 9://subu
			aluout=directToInt(intToHex(inA))-directToInt(intToHex(inB));
		break;
	}
    //cout<<IDEX.opcode<<" "<<aluout<<"  ";
	if(aluout==0){
		IDEX.zero=1;
	}else{
		IDEX.zero=0;
	}

	IDEX.aluout=aluout;
}

long msbPC(){
	long msb=PC & (~(268435455));
	//cout<<endl<<msb<<endl;
	return msb;
}

void earlyBranch(){
    if(IFID.opcode=="beq" && reg[IFID.rs]==reg[IFID.rt]){
        PC=IDEX.target-1;
        IFID.branch=0;
        ifflush=true;
    }
}

void jmp(){
	if(jump){
		PC=address; // was addr+msbPC()
	}
}

int lbl_trans(string label){
    for(int i=0; i<lbl_max; i++){
        if(label_nm[i]==label){//search for existing label
            return i;
        }
    }
    return -1;
}

int mem_trans(unsigned int addr){
    for(int i=0; i<mmp; i++){
        if(memAddress[i]==addr){//search for existing mem address
            return i;
        }
    }
    //else
    for(int i=0; i<mmp; i++){//assign new mem address
        if(memAddress[i]==0){
            memAddress[i]=addr;
            return i;
        }
    }
    exit(-3);//OUT OF MEMORY
}

void memory(){
	if(EXMEM.memread){
		EXMEM.mem_out=MEM[mem_trans(EXMEM.aluout)];
	}

	if(EXMEM.memwrite){
		MEM[mem_trans(EXMEM.aluout)]=EXMEM.mem_in;
	}
}

void fillMem(){
    reg[reg_trans("gp")]=hex_dec("10008000");
    reg[reg_trans("sp")]=hex_dec("7FFFFFFC");
}

void print_monitors(bool endd){
    ofstream fout;
    fout.open("output.txt", ios::app);
    if (!fout.is_open()) {
		exit(-4);
	}

	if(endd){
        fout<<endl<<"-----Final State-----"<<endl;
	}else{
        fout<<endl<<"-----Cycle "<<cycles<<"-----"<<endl;
	}
	fout<<"Registers:"<<endl;
	/*
	if(endd)
        fout<<trim(intToHex(PC*4-4))<<'\t';
    else
        fout<<trim(intToHex(PC*4-4))<<'\t';*/

    if((EXMEM.opcode=="beq" && EXMEM.zero && EXMEM.branch) || (EXMEM.opcode=="bne" && !EXMEM.zero && EXMEM.branch)){
            fout<<trim(intToHex(IDEX.PC1*4))<<'\t';//mon 2
        }else
            fout<<trim(intToHex((PC*4-4)))<<'\t';//mon 2

	for(int i=0; i<32; i++){
        if(reg[i]==0){
            fout<<"0"<<'\t';
        }else{
            fout<<trim(intToHex(reg[i]))<<'\t';
        }
	}

	if(!endd){
        fout<<endl<<endl<<"Monitors:"<<endl;
        //fout<<endl<<type<<endl;
        if((EXMEM.opcode=="beq" && EXMEM.zero && EXMEM.branch && 0) || (EXMEM.opcode=="bne" && !EXMEM.zero && EXMEM.branch && 0)){
            fout<<trim(intToHex(EXMEM.target*4))<<'\t';//mon 1
        }else
            fout<<trim(intToHex((PC)*4))<<'\t';//mon 1

        if((EXMEM.opcode=="beq" && EXMEM.zero && EXMEM.branch && 0) || (EXMEM.opcode=="bne" && !EXMEM.zero && EXMEM.branch && 0)){
            fout<<trim(intToHex(IDEX.PC1*4))<<'\t';//mon 2
        }else
            fout<<trim(intToHex((PC*4-4)))<<'\t';//mon 2

        //fout<<trim(intToHex(PC*4-4))<<'\t';//mon 2
        fout<<deformater(IFID.instr, IFID.opcode)<<'\t';//mon 3
        fout<<EXMEM.string_lbl<<'\t';//mon 4
        fout<<'$'<<mipsRegisters[IDEX.rs]<<'\t';//mon 5
        fout<<'$'<<mipsRegisters[IDEX.rt]<<'\t';//mon 6
        fout<<'$'<<mipsRegisters[MEMWB.wr]<<'\t';//mon 7
        fout<<trim(intToHex(MEMWB.write_data))<<'\t';//mon 8
        fout<<trim(intToHex(IDEX.readA))<<'\t';//mon 9
        fout<<trim(intToHex(IDEX.readB))<<'\t';//mon 10
        fout<<trim(intToHex(IDEX.immed))<<'\t';//mon 11
        fout<<'$'<<mipsRegisters[IDEX.rs]<<'\t';//mon 12
        fout<<'$'<<mipsRegisters[IDEX.rt]<<'\t';//mon 13
        fout<<'$'<<mipsRegisters[IDEX.rt]<<'\t';//mon 14
        fout<<'$'<<mipsRegisters[IDEX.rd]<<'\t';//mon 15
        fout<<trim(intToHex(IDEX.readA))<<'\t';//mon 16 ALLAGI
        if(!EXMEM.ALUsrc)
            fout<<trim(intToHex(EXMEM.readB))<<'\t';//mon 17 ALLAGI
        else
            fout<<trim(intToHex(EXMEM.immed))<<'\t';//mon 17
        fout<<trim(intToHex(EXMEM.aluout))<<'\t';//mon 18
        fout<<trim(intToHex(EXMEM.readB))<<'\t';//mon 19 ALLAGI
        fout<<trim(intToHex(MEMWB.aluout))<<'\t';//mon 20
        fout<<trim(intToHex(MEMWB.mem_in))<<'\t';//mon 21
        fout<<trim(intToHex(MEMWB.mem_out))<<'\t';//mon 22
        fout<<trim(intToHex(MEMWB.aluout))<<'\t';//mon 23
        fout<<'$'<<mipsRegisters[MEMWB.wr]<<'\t';//mon 24
        fout<<'$'<<mipsRegisters[MEMWB.wr]<<'\t';//mon 25
        if(MEMWB.memtoreg)
            fout<<trim(intToHex(MEMWB.mem_out))<<'\t';//mon 26
        else
            fout<<trim(intToHex(MEMWB.aluout))<<'\t';//mon 26
        fout<<hazard<<'\t';//mon 27
        fout<<forwarding<<'\t';//mon 28

	}

	fout<<endl<<endl<<"Memory State:"<<endl;

	if(MEMWB.opcode=="sw"){
        fout<<trim(intToHex(MEM[mem_trans(aluout)]));
	}

    if(endd){
        for(int i=0; i<mmp; i++){
            if(memAddress[i]!=0){
                fout<<trim(intToHex(MEM[i]))<<'\t';
            }
        }
    }

    fout<<endl;

    if(!endd){
        fout<<endl<<"Pipeline Stages:"<<endl;
        fout<<deformater(IFID.instr, IFID.opcode)<<'\t'<<deformater(IDEX.instr, IDEX.opcode)<<'\t'<<deformater(EXMEM.instr, EXMEM.opcode)<<'\t'<<deformater(MEMWB.instr, MEMWB.opcode)<<'\t'<<deformater(instr_evicted, opcode)<<'\t'<<endl;
    }

    if(endd){
        fout<<endl<<"Total Cycles:"<<endl<<cycles-1;
        fout<<endl<<endl<<"Total Execution Time: "<<endl<<userTime*1000000000<<" (ns)";
    }

	fout.close();
}

void monitors(){
    if(cycles==cyc_to_print[cyc_count]){
        cyc_count++;
        print_monitors(false);
    }else{
        if(cyc_to_print[cyc_count]==0){
            print_monitors(false);
        }
    }
}

void init_out(){
    ofstream fout;
    fout.open("output.txt");
    if (!fout.is_open()) {
		exit(-4);
	}
	fout<<"Name: Marios Christoforou"<<endl<<"ID: -"<<endl;
	fout.close();
}

void IFflush(bool fl){
    if(fl){
        IFID.ALUsrcA=0;
        IFID.ALUsrcB=0;
        IFID.immed=0;
        IFID.instr="sll$zero,$zero,0";
        IFID.memread=0;
        IFID.memwrite=0;
        IFID.opcode="sll";
        IFID.rd=0;
        IFID.rs=0;
        IFID.rt=0;
        IFID.regwrite=0;
        IFID.string_lbl="-";
        IFID.branch=0;
        IFID.target=0;
        IFID.type="I";
        IFID.wr=0;
        ifflush=false;
    }
}

void bubbles(){
    IFID.memwrite=0;
    IFID.regwrite=0;
    IFID.branch=0;

    IDEX.memwrite=0;
    IDEX.regwrite=0;
    IDEX.branch=0;
}

void hazardDetectionAndForwarding(){
    IDEX.ALUsrcA=0;
    IDEX.ALUsrcB=0;
    hazard=0;
    forwarding=0;

    if(MEMWB.wr==IDEX.rs && MEMWB.wr!=0){
        forwarding=1;
        if(MEMWB.regwrite){
            IDEX.ALUsrcA=2;
            MEMWB.fw=MEMWB.aluout;
            if(MEMWB.opcode=="lw"){
                MEMWB.fw=MEMWB.mem_out;
            }
            hazard=1;
        }
    }

    if(MEMWB.wr==IDEX.rt && MEMWB.wr!=0){
        forwarding=1;
        if(MEMWB.regwrite){
            IDEX.ALUsrcB=2;
            MEMWB.fw=MEMWB.aluout;
            if(MEMWB.opcode=="lw"){
                MEMWB.fw=MEMWB.mem_out;
            }
            hazard=1;
        }
    }

    if(EXMEM.wr==IDEX.rs && EXMEM.wr!=0){//protereotita to EX hazard
        forwarding=1;
        if(EXMEM.regwrite){
            IDEX.ALUsrcA=1;
            hazard=1;
        }
    }

    //cout<<EXMEM.wr<<"  "<<IDEX.rt<<" - ";
    if(EXMEM.wr==IDEX.rt && EXMEM.wr!=0 && EXMEM.regwrite){//protereotita to EX hazard
        forwarding=1;
        if(EXMEM.regwrite){
            IDEX.ALUsrcB=1;
            hazard=1;
        }
    }

    //LOAD USE CHECK

    if(IDEX.opcode=="lw" && (IDEX.wr==IFID.rs || IDEX.wr==IFID.rt)){
        PC--;
        nextPC--;
        IFflush(true);
        hazard=1;
    }

    //CONTROL HAZARDS

    if(IFID.opcode=="beq" && reg[IFID.rs]==reg[IFID.rt]){
        PC=IFID.target-1;
        IFID.branch=0;
        ifflush=true;
        hazard=1;
    }

    if(IFID.opcode=="bne" && reg[IFID.rs]!=reg[IFID.rt]){
        PC=IFID.target-1;//kai oxi to next pc
        IFID.branch=0;
        ifflush=true;
        hazard=1;
    }
}

void brnch(){
    //target=2;
    if(IDEX.branch && IDEX.zero && IDEX.opcode=="beq"){
        PC=IDEX.target-1;
        //cout<<"YESS";
        //bubbles();
    }
    if(IDEX.branch && !IDEX.zero && IDEX.opcode=="bne"){
        PC=IDEX.target-1;
        //bubbles();
        //cout<<"YESS";
    }
}

void update(){

    opcode=MEMWB.opcode;
    instr_evicted=MEMWB.instr;

    MEMWB.rs=EXMEM.rs;
    MEMWB.rt=EXMEM.rt;
    MEMWB.rd=EXMEM.rd;
    MEMWB.wr=EXMEM.wr;
    MEMWB.target=EXMEM.target;
    MEMWB.PC1=EXMEM.PC1;
    MEMWB.instr=EXMEM.instr;
    MEMWB.readA=EXMEM.readA;
    MEMWB.readB=EXMEM.readB;
    MEMWB.regdst=EXMEM.regdst;
    MEMWB.branch=EXMEM.branch;
    MEMWB.memread=EXMEM.memread;
    MEMWB.memwrite=EXMEM.memwrite;
    MEMWB.memtoreg=EXMEM.memtoreg;
    MEMWB.regwrite=EXMEM.regwrite;
    MEMWB.ALUsrc=EXMEM.ALUsrc;
    MEMWB.ALUsrcA=EXMEM.ALUsrcA;
    MEMWB.ALUsrcB=EXMEM.ALUsrcB;
    MEMWB.immed=EXMEM.immed;
    MEMWB.aluop=EXMEM.aluop;
    MEMWB.aluout=EXMEM.aluout;
    MEMWB.mem_in=EXMEM.mem_in;
    MEMWB.mem_out=EXMEM.mem_out;
    MEMWB.write_data=EXMEM.write_data;
    MEMWB.zero=EXMEM.zero;
    MEMWB.opcode=EXMEM.opcode;
    MEMWB.type=EXMEM.type;
    MEMWB.string_lbl=EXMEM.string_lbl;


    EXMEM.rs=IDEX.rs;
    EXMEM.rt=IDEX.rt;
    EXMEM.rd=IDEX.rd;
    EXMEM.wr=IDEX.wr;
    EXMEM.target=IDEX.target;
    EXMEM.PC1=IDEX.PC1;
    EXMEM.instr=IDEX.instr;
    EXMEM.readA=IDEX.readA;
    EXMEM.readB=IDEX.readB;
    EXMEM.regdst=IDEX.regdst;
    EXMEM.branch=IDEX.branch;
    EXMEM.memread=IDEX.memread;
    EXMEM.memwrite=IDEX.memwrite;
    EXMEM.memtoreg=IDEX.memtoreg;
    EXMEM.regwrite=IDEX.regwrite;
    EXMEM.ALUsrc=IDEX.ALUsrc;
    EXMEM.ALUsrcA=IDEX.ALUsrcA;
    EXMEM.ALUsrcB=IDEX.ALUsrcB;
    EXMEM.immed=IDEX.immed;
    EXMEM.aluop=IDEX.aluop;
    EXMEM.aluout=IDEX.aluout;
    EXMEM.mem_in=IDEX.mem_in;
    EXMEM.mem_out=IDEX.mem_out;
    EXMEM.write_data=IDEX.write_data;
    EXMEM.zero=IDEX.zero;
    EXMEM.opcode=IDEX.opcode;
    EXMEM.type=IDEX.type;
    EXMEM.string_lbl=IDEX.string_lbl;


    IDEX.rs=IFID.rs;
    IDEX.rt=IFID.rt;
    IDEX.rd=IFID.rd;
    IDEX.wr=IFID.wr;
    IDEX.target=IFID.target;
    IDEX.PC1=IFID.PC1;
    IDEX.instr=IFID.instr;
    IDEX.readA=IFID.readA;
    IDEX.readB=IFID.readB;
    IDEX.regdst=IFID.regdst;
    IDEX.branch=IFID.branch;
    IDEX.memread=IFID.memread;
    IDEX.memwrite=IFID.memwrite;
    IDEX.memtoreg=IFID.memtoreg;
    IDEX.regwrite=IFID.regwrite;
    IDEX.ALUsrc=IFID.ALUsrc;
    IDEX.ALUsrcA=IFID.ALUsrcA;
    IDEX.ALUsrcB=IFID.ALUsrcB;
    IDEX.immed=IFID.immed;
    IDEX.aluop=IFID.aluop;
    IDEX.aluout=IFID.aluout;
    IDEX.mem_in=IFID.mem_in;
    IDEX.mem_out=IFID.mem_out;
    IDEX.write_data=IFID.write_data;
    IDEX.zero=IFID.zero;
    IDEX.opcode=IFID.opcode;
    IDEX.type=IFID.type;
    IDEX.string_lbl=IFID.string_lbl;
}

int main(int argc, char *argv[])
{
    int i=0;
	cout<<"Command file name: ";
    cin>>file_name;
    cout<<"Cycles to print in ascending order (-1 to continue, 0 for all): "<<endl;
    do{
        cin>>cyc_to_print[i];
        i++;
    }while(cyc_to_print[i-1]!=-1 && cyc_to_print[i-1]!=0);


    preparser();
    init_out();
    fillMem();
	mainline=starter()+1;

	start_time=clock();
	while(1){

		/*instr_reg(mainline+PC);
		control_unit();
		target_calc();//unneeded
		reg_file();
		ALU();
		memory();
		reg_file();
		brnch();
		jmp();//unused
        monitors();
        cycles++;*/

        nextPC=mainline+PC;

        IFflush(ifflush);
        reg_file();
        memory();
        hazardDetectionAndForwarding();
        ALU();
        //brnch();
        reg_file();
        //earlyBranch();
        control_unit();
        update();
        instr_reg(nextPC);
        monitors();
        //brnch();
        cycles++;
	}

    print_monitors(true);
    return 0;
}

//0 ALL GOOD - 1 NO FILE - 2 INVALID COMMAND - 3 OUT OF MEMORY - 4 OUT FILE ERROR - 5 PREPARSER ERROR - 6 OUT OF LABEL SPACE
