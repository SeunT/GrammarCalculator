
#include <iostream>
#include <istream>
#include <vector>
#include <string>
#include <cctype>

#include "lexer.h"
#include "inputbuf.h"

using namespace std;

// Lexer modified for FIRST & FOLLOW project

string reserved[] = { "END_OF_FILE", "ARROW", "HASH", "DOUBLEHASH", "ID", "ERROR" };

void Token::Print()
{
    cout << "{" << this->lexeme << " , "
        << reserved[(int)this->token_type] << " , "
        << this->line_no << "}\n";
}

LexicalAnalyzer::LexicalAnalyzer()
{
    this->line_no = 1;
    tmp.lexeme = "";
    tmp.line_no = 1;
    tmp.token_type = ERROR;
}

bool LexicalAnalyzer::SkipSpace()
{
    char c;
    bool space_encountered = false;

    input.GetChar(c);
    line_no += (c == '\n');

    while (!input.EndOfInput() && isspace(c)) {
        space_encountered = true;
        input.GetChar(c);
        line_no += (c == '\n');
    }

    if (!input.EndOfInput()) {
        input.UngetChar(c);
    }
    return space_encountered;
}

Token LexicalAnalyzer::ScanId()
{
    char c;
    input.GetChar(c);

    if (isalpha(c)) {
        tmp.lexeme = "";
        while (!input.EndOfInput() && isalnum(c)) {
            tmp.lexeme += c;
            input.GetChar(c);
        }
        if (!input.EndOfInput()) {
            input.UngetChar(c);
        }
        tmp.line_no = line_no;
        tmp.token_type = ID;
    }
    else {
        if (!input.EndOfInput()) {
            input.UngetChar(c);
        }
        tmp.lexeme = "";
        tmp.token_type = ERROR;
    }
    return tmp;
}


TokenType LexicalAnalyzer::UngetToken(Token tok)
{
    tokens.push_back(tok);;
    return tok.token_type;
}

Token LexicalAnalyzer::GetToken()
{
    char c;

  
    if (!tokens.empty()) {
        tmp = tokens.back();
        tokens.pop_back();
        return tmp;
    }


    SkipSpace();
    tmp.lexeme = "";
    tmp.line_no = line_no;
    tmp.token_type = END_OF_FILE;
    if (!input.EndOfInput())
        input.GetChar(c);
    else
        return tmp;

    switch (c) {
    case '-':
        input.GetChar(c);
        if (c == '>') {
            tmp.token_type = ARROW;
        }
        else {
            if (!input.EndOfInput()) {
                input.UngetChar(c);
            }
            tmp.token_type = ERROR;
        }
        return tmp;
    case '#':
        input.GetChar(c);
        if (c == '#') {
            tmp.token_type = DOUBLEHASH;
        }
        else {
            if (!input.EndOfInput()) {
                input.UngetChar(c);
            }
            tmp.token_type = HASH;
        }
        return tmp;
    default:
        if (isalpha(c)) {
            input.UngetChar(c);
            return ScanId();
        }
        else if (input.EndOfInput())
            tmp.token_type = END_OF_FILE;
        else
            tmp.token_type = ERROR;

        return tmp;
    }
}
