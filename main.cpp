#include<iostream>
#include<chrono>
#include<string>
using namespace std;
using namespace std::chrono;
template<typename T> class Node{
public:
    T data;
    Node* next;

    Node(T c){
        data=c;
        next=NULL;
    }
};

// Stack implementation
template <typename T> class Stack{
public:
    Node<T> * head;

    Stack(){
        head=NULL;

    }
    bool empty(){
        return head==NULL;
    }
    void push(T c){
        if(head==NULL){
            head=new Node<T> (c);

        }else{
            Node<T>* temp=head;
            head=new Node<T>(c);
            head->next=temp;
        }
    }
    void pop(){
        head=head->next;
    }
    T top(){
        return head->data;
    }
};


int positionOfOperator(char c,string formula){
    formula=formula.substr(1);
    formula.pop_back();
    Stack<char> st;
    for(int i=0;i<formula.length();i++){
        st.push(formula[i]);
    }
    bool check= true;
    int count=0;
    int pos=formula.length();
    while(st.empty()==false){
        if(check==true && count==0 && st.top()==c){
            break;
        }
        if(st.top()==')'){
            count++;
            check=false;
        }
        if(st.top()=='('){
            count--;
            check=true;
        }
        st.pop();
        pos--;
    }
    return pos;
}
bool isOperator(char c){
    return c=='^' || c=='+' || c=='>' || c=='~';
}
bool isCharacter(char c){
    return (c>=65 && c<=90) || (c>=97 && c<=122);
}
//bool validFormula(string line){
//    if(line.length()==1 && !(isCharacter(line[0]))){
//        return false;
//    }
//    for(int i=0;i<line.length()-1;i++){
//
//    }
//}

bool andIntroduction(string* proof_lines,string currentLine,int currentLineNumber,int line1Ref,int line2Ref){
    if(line1Ref>=currentLineNumber || line2Ref>=currentLineNumber){
        return false;
    }
    string line1Statement=proof_lines[line1Ref-1].substr(0,proof_lines[line1Ref-1].find("/"));
    string line2Statement=proof_lines[line2Ref-1].substr(0,proof_lines[line2Ref-1].find("/"));
    string expectedStatement="(";
    expectedStatement+=line1Statement+"^"+line2Statement+")";
    if(expectedStatement==currentLine){
        return true;
    }else{
        return false;
    }

}
bool implication_elimination(string* proof_lines,string currentLine,int currentLineNumber,int line1Ref,int line2Ref){
    if(line1Ref>=currentLineNumber || line2Ref>=currentLineNumber){
        return false;
    }
    string line1Statement=proof_lines[line1Ref-1].substr(0,proof_lines[line1Ref-1].find("/"));
    string line2Statement=proof_lines[line2Ref-1].substr(0,proof_lines[line2Ref-1].find("/"));
    string expectedConclusion=line1Statement.substr(positionOfOperator('>',line1Statement)+1,line1Statement.length()-1-line1Statement.find(">")-1);
    string hypothesis=line1Statement.substr(1, positionOfOperator('>',line1Statement)-1);
    if(hypothesis==line2Statement && expectedConclusion==currentLine){
        return true;
    }else{
        return false;
    }
}
bool orIntroduction1(string* proof_lines,string currentLine,int currentLineNumber,int line1Ref){
    if(line1Ref>=currentLineNumber){
        return false;
    }
    string line1Statement=proof_lines[line1Ref-1].substr(0,proof_lines[line1Ref-1].find("/"));
    string expectedOutputPart="("+line1Statement+"+";
    int l=currentLine.find(expectedOutputPart);
    if(l==0 && currentLine.length()>expectedOutputPart.length()+1){
        return true;
    }else{
        return false;
    }
}
bool orIntroduction2(string* proof_lines,string currentLine,int currentLineNumber,int line1Ref){
    if(line1Ref>=currentLineNumber){
        return false;
    }
    string line1Statement=proof_lines[line1Ref-1].substr(0,proof_lines[line1Ref-1].find("/"));
    string expectedOutputPart="+"+line1Statement+")";
    int l=currentLine.find(expectedOutputPart);
    if(l==(currentLine.length()-expectedOutputPart.length()) && currentLine.length()>expectedOutputPart.length()+1){
        return true;
    }else{
        return false;
    }
}
bool andElimination1(string* proof_lines,string currentLine,int currentLineNumber,int line1Ref){
    if(line1Ref>=currentLineNumber){
        return false;
    }
    string line1Statement=proof_lines[line1Ref-1].substr(0,proof_lines[line1Ref-1].find("/"));
    string expectedOutput=line1Statement.substr(1, positionOfOperator('^',line1Statement)-1);
   // expectedOutput.pop_back();
    if(expectedOutput==currentLine){
        return true;
    }else{
        return false;
    }
}
bool andElimination2(string* proof_lines,string currentLine,int currentLineNumber,int line1Ref){
    if(line1Ref>=currentLineNumber){
        return false;
    }
    string line1Statement=proof_lines[line1Ref-1].substr(0,proof_lines[line1Ref-1].find("/"));
    string expectedOutput=line1Statement.substr(positionOfOperator('^',line1Statement)+1);
    expectedOutput.pop_back();
    if(expectedOutput==currentLine){
        return true;
    }else{
        return false;
    }
}
bool modusTollens(string* proof_lines,string currentLine,int currentLineNumber,int line1Ref,int line2Ref){
    if(line1Ref>=currentLineNumber || line2Ref>=currentLineNumber){
        return false;
    }
    string line1Statement=proof_lines[line1Ref-1].substr(0,proof_lines[line1Ref-1].find("/"));//implication
    string line2Statement=proof_lines[line2Ref-1].substr(0,proof_lines[line2Ref-1].find("/"));//negation
    string expectedOutput="(~";
    expectedOutput+=line1Statement.substr(1,positionOfOperator('>',line1Statement)-1);
    expectedOutput+=")";
    string rhs=line1Statement.substr(positionOfOperator('>',line1Statement)+1);
    rhs.pop_back();
    if(("(~"+rhs+")")==line2Statement && expectedOutput==currentLine){
        return true;
    }else{
        return false;
    }
}


bool proof_Evaluator(string* proof_lines,int number_of_lines){

    for(int i=0;i<number_of_lines;i++){

        int line1,line2;

        string line=proof_lines[i];
        string ruleTemp=line.substr(line.find("/")+1);
        string statement=line.substr(0,line.find("/"));
        //string line_ref=ruleTemp.substr()
        if(ruleTemp.length()>1){
            string rule=ruleTemp.substr(0,ruleTemp.find("/"));
        }

        if(ruleTemp=="P"){
            continue;
        }
        string rule=ruleTemp.substr(0,ruleTemp.find("/"));
        ruleTemp=ruleTemp.substr(ruleTemp.find(rule)+rule.length()+1);
        if(rule=="^i" || rule==">e" || rule=="MT"){
            string lineRef1=ruleTemp.substr(0,ruleTemp.find("/"));
            string lineRef2=ruleTemp.substr(ruleTemp.find("/")+1);
            line1= stoi(lineRef1);
            line2= stoi(lineRef2);
            if(rule=="^i"){
                bool b= andIntroduction(proof_lines,statement,i+1,line1,line2);
                if(b==false){
                    return false;
                }
            }
            if(rule==">e"){
                bool b=implication_elimination(proof_lines,statement,i+1,line1,line2);
                if(b==false){
                    return false;
                }
            }
            if(rule=="MT"){
                bool b= modusTollens(proof_lines,statement,i+1,line1,line2);
                if(b==false){
                    return false;
                }
            }
        }else{
            string lineRef1=ruleTemp.substr(0,ruleTemp.find("/"));
            line1= stoi(lineRef1);
            if(rule=="+i1"){
                bool b= orIntroduction1(proof_lines,statement,i+1,line1);
                if(b==false){
                    return false;
                }
            }else if(rule=="+i2"){
                bool b= orIntroduction2(proof_lines,statement,i+1,line1);
                if(b==false){
                    return false;
                }

            }else if(rule=="^e1"){
                bool b= andElimination1(proof_lines,statement,i+1,line1);
                if(b==false){
                    return false;
                }

            }else if(rule=="^e2"){
                bool b= andElimination2(proof_lines,statement,i+1,line1);
                if(b==false){
                    return false;
                }
            }

        }






    }



    return true;
}

int main() {
    int number_of_lines;
    cin>>number_of_lines;
    string* proof_lines=new string[number_of_lines];
    for(int i=0;i<number_of_lines;i++){
        cin>>proof_lines[i];
    }
    cout<<endl;
    auto start = high_resolution_clock::now();
    bool validity= proof_Evaluator(proof_lines,number_of_lines);
    auto stop = high_resolution_clock::now();
    if(validity== true){
        cout<<"Valid Proof"<<endl;
    }else{
        cout<<"Invalid proof"<<endl;
    }
    cout<<endl;
    auto duration = duration_cast<microseconds>(stop - start);
    cout<<"Execution time: "<<duration.count()<<"\xC2\xB5"<<endl;



}
