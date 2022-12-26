//
// Analyzer for simple C programs.  This component performs
// type checking.  The analyzer returns a string denoting
// success or failure. The string "success" if the input 
// program is legal, otherwise the string "type_error: ..." 
// is returned denoting an invalid simple C program.
//
// Modified by:
//   Sergio Ambelis Diaz
//
// Original author:
//   Prof. Joe Hummel
//   U. of Illinois, Chicago
//   CS 341, Spring 2022
//

namespace compiler

module checker =
  //
  // NOTE: all functions in the module must be indented.
  //


  //
  // matchToken
  //
  let private matchToken expected_token (tokens: string list) =
    //
    // if the next token matches the expected token,  
    // keep parsing by returning the rest of the tokens.
    // Otherwise throw an exception because there's a 
    // syntax error, effectively stopping compilation:
    //
    // NOTE: identifier, int_literal and str_literal
    // are special cases because they are followed by
    // the name or literal value. In these cases exact
    // matching will not work, so we match the start 
    // of the token in these cases.
    //
    let next_token = List.head tokens 

    if expected_token = "identifier" && next_token.StartsWith("identifier") then
      //
      // next_token starts with identifier, so we have a match:
      //
      List.tail tokens
    elif expected_token = "int_literal" && next_token.StartsWith("int_literal") then
      //
      // next_token starts with int_literal, so we have a match:
      //
      List.tail tokens
    elif expected_token = "str_literal" && next_token.StartsWith("str_literal") then
      //
      // next_token starts with str_literal, so we have a match:
      //
      List.tail tokens
    elif expected_token = "real_literal" && next_token.StartsWith("real_literal") then
      //
      // next_token starts with real_literal, so we have a match:
      //
      List.tail tokens
    elif expected_token = next_token then  
      List.tail tokens
    else
      failwith ("expecting " + expected_token + ", but found " + next_token)


  //  helper which returns the type
  let rec get_type name L = 
    match L with
    | []       -> failwith ("variable '" + name + "' undefined")
    | (var, rtype)::tl when name = var  -> rtype 
    | (var, rtype)::tl                  -> get_type name tl 
      



  //
  // <expr-value> -> identifier
  //               | int_literal
  //               | str_literal
  //               | true
  //               | false
  //
  let rec private expr_value tokens symbolTable =
    let next_token = List.head tokens
    // look at the types, and return a tuple of bool
    if next_token = "false" then
      let T2 = matchToken "false" tokens 
      (T2, "bool")
    elif next_token = "true" then
      let T2 = matchToken "true" tokens
      (T2, "bool")
    // look at the types, and return a tuple of type to declare
    elif next_token.StartsWith("identifier") then 
      let T2 = matchToken "identifier" tokens  // returns list 
      let name = next_token.Substring (String.length("identifier:"))
      let rType = get_type name symbolTable
      (T2, rType)
    elif next_token.StartsWith("int_literal") then
      let T2 = matchToken "int_literal" tokens
      (T2, "int")
    elif next_token.StartsWith("real_literal") then
      let T2 = matchToken "real_literal" tokens
      (T2, "real")
    elif next_token.StartsWith("str_literal") then
      let T2 = matchToken "str_literal" tokens
      (T2, "str")
    else
      failwith ("expecting identifier or literal, but found " + next_token)


  //
  // <expr-op> -> +
  //            | -
  //            | *
  //            | /
  //            | ^
  //            | <
  //            | <=
  //            | >
  //            | >=
  //            | ==
  //            | !=
  //
  let rec private expr_op tokens = 
    let next_token = List.head tokens
    // Check for expression operation
    if next_token = "+"  ||
       next_token = "-"  ||
       next_token = "*"  ||
       next_token = "/"  ||
       next_token = "^"  ||
       next_token = "<"  ||
       next_token = "<=" ||
       next_token = ">"  ||
       next_token = ">=" ||
       next_token = "==" ||
       next_token = "!=" then
      
      let T2 = matchToken next_token tokens
      T2
    else
      // error
      failwith ("expecting expression operator, but found " + next_token)


  //
  // <expr> -> <expr-value> <expr-op> <expr-value>
  //         | <expr-value>
  //
  let rec private expr tokens symbolTable = 
    //
    // first we have to match expr-value, since both
    // rules start with this:
    //
    let (T2, left_type) = expr_value tokens symbolTable
    //
    // now let's see if there's more to the expression:
    //
    let next_token = List.head T2
    //
    if next_token = "+"  ||
       next_token = "-"  ||
       next_token = "*"  ||
       next_token = "/"  ||
       next_token = "^"  ||
       next_token = "<"  ||
       next_token = "<=" ||
       next_token = ">"  ||
       next_token = ">=" ||
       next_token = "==" ||
       next_token = "!=" then
 
      let T3 = expr_op T2
      let (T4, right_type) = expr_value T3 symbolTable
    // issues a warning for expressions involving “==” with operands of type “real”
      if left_type = "real" && right_type = "real" && next_token = "==" then
        printfn "warning: comparing real numbers with == may never be true"
      else // return empty tuple
        ()

      // arithmetic operations: check for real types or int type
      if next_token = "+" ||
         next_token = "-"  ||
         next_token = "*"  ||
         next_token = "/"  ||
         next_token = "^"  then // compare right and left to see if same type
        if left_type = "real" && right_type = "real" || 
           left_type = "int" && right_type = "int" then
          (T4, left_type)
        else // if left and right type are not same type then output error
          failwith ("operator " + next_token + " must involve 'int' or 'real'")
      // comparison operators, result in valid bool
      elif left_type = right_type then  // check for bool
        (T4, "bool")
      else   // error, our types did not match
        failwith ("type mismatch '" + left_type + "' " + next_token + " '" + right_type + "'")

    else
      (T2, left_type)



  //
  // <empty> -> ;
  //
  let rec private empty tokens = 
    let T2 = matchToken ";" tokens
    T2

  //
  // <vardecl> -> int identifier ;
  //
  let rec private vardecl tokens = 
    let next_token = List.head tokens
    if next_token = "int" ||  // if next token is int or real
       next_token = "real" then
      let T2 = matchToken next_token tokens  
      let T3 = matchToken "identifier" T2
      let T4 = matchToken ";" T3
      T4
    else
     failwith ("operator " + next_token + " must involve 'int' or 'real'")


  //
  // <input> -> cin >> identifier ;
  //
  let rec private input tokens symbolTable = 
    let T2 = matchToken "cin" tokens
    let T3 = matchToken ">>" T2
    let T4 = matchToken "identifier" T3
    let next_token = List.head T3
    // Check to so if next token is defined:
    //   We take the substring of token after >> 
    //   Then it's length of "indentifier" or [11..]
    //   We end up with just the name of that token
    let name = next_token.[11..]
    //   We use the get_type helper function to check for type
    //   Else we output an error type iis undefined
    let rType = get_type name symbolTable // use the get type function
    let T6 = matchToken ";" T4
    T6


  //
  // <output-value> -> <expr-value>
  //                 | endl
  //
  let rec private output_value tokens symbolTable = 
    let next_token = List.head tokens
    // case where if we meet endl
    if next_token = "endl" then
      let T2 = matchToken "endl" tokens
      T2
    else // else get new token and type
      let (T2, expr_type) = expr_value tokens symbolTable
      T2


  //
  // <output> -> cout << <output-value> ;
  //
  let rec private output tokens symbolTable = 
    let T2 = matchToken "cout" tokens
    let T3 = matchToken "<<" T2
    let T4 = output_value T3 symbolTable
    let T5 = matchToken ";" T4
    T5


  //
  // <assignment> -> identifier = <expr> ;
  //
  let rec private assignment tokens symbolTable = 
    let next = List.head tokens
    let T2 = matchToken "identifier" tokens
    // find the name of the prior variable (left_variable)
    let name = next.Substring (String.length("identifier:"))
    // use the id_type to get type of the prior variable
    let id_type = get_type name symbolTable 
    let T3 = matchToken "=" T2
    // get new token and type
    let (T4, expr_type) = expr T3 symbolTable
    let T5 = matchToken ";" T4        
    if expr_type = id_type then // check if prior type and new type match
      T5
    elif expr_type = "int" && id_type = "real" then
      T5
    else
      failwith ("cannot assign '" + expr_type + "' to variable of type '" + id_type + "'")


  //
  // <stmt> -> <empty>
  //         | <vardecl>
  //         | <input>
  //         | <output>
  //         | <assignment>
  //         | <ifstmt>
  //
  let rec private stmt tokens symbolTable = 
    let next_token = List.head tokens
    //
    // use the next token to determine which rule
    // to call; if none match then it's a syntax
    // error:
    //
    if next_token = ";" then
      let T2 = empty tokens 
      T2
    elif next_token = "int" then
      let T2 = vardecl tokens 
      T2
    elif next_token = "real" then
      let T2 = vardecl tokens
      T2
    elif next_token = "cin" then
      let T2 = input tokens symbolTable
      T2
    elif next_token = "cout" then
      let T2 = output tokens symbolTable
      T2
    elif next_token.StartsWith("identifier") then
      let T2 = assignment tokens symbolTable
      T2
    elif next_token = "if" then
      let T2 = ifstmt tokens symbolTable
      T2
    else
      failwith ("expecting statement, but found " + next_token)
  //
  // <ifstmt> -> if ( <condition> ) <then-part> <else-part>
  //
  and private ifstmt tokens symbolTable = 
    let T2 = matchToken "if" tokens
    let T3 = matchToken "(" T2
    let T4 = condition T3 symbolTable
    let T5 = matchToken ")" T4
    let T6 = then_part T5 symbolTable
    let T7 = else_part T6 symbolTable
    T7

  //
  // <condition> -> <expr>
  //
  and private condition tokens symbolTable= 
    let (T2, expr_type) = expr tokens symbolTable
    if expr_type <> "bool" then // condition to check if not bool
      failwith ("if condition must be 'bool', but found '" + expr_type + "'")
    else
      T2

  
  // <then-part> -> <stmt>
  //
  and private then_part tokens symbolTable = 
    let T2 = stmt tokens symbolTable
    T2
  //
  // <else-part> -> else <stmt>
  //            | EMPTY
  
  and private else_part tokens symbolTable = 
    let next_token = List.head tokens
    //
    if next_token = "else" then
      let T2 = matchToken "else" tokens
      let T3= stmt T2 symbolTable
      T3
    else
      // EMPTY, do nothing but return tokens back
      tokens


  //
  // <morestmts> -> <stmt> <morestmts>
  //              | EMPTY
  //
  let rec private morestmts tokens symbolTable = 
    //
    // if the next token denotes the start of a stmt 
    // then process stmt and morestmts, otherwise apply
    // EMPTY
    //
    let next_token = List.head tokens
    //
    if next_token = ";"    ||
       next_token = "int"  ||
       next_token = "cin"  ||
       next_token = "cout" ||
       next_token = "real" ||
       next_token.StartsWith("identifier") ||
       next_token = "if" then
      //
      let T2 = stmt tokens symbolTable
      let T3 = morestmts T2 symbolTable
      T3
    else 
      // EMPTY => do nothing, just return tokens back
      tokens


  //
  // <stmts> -> <stmt> <morestmts>
  // 
  let rec private stmts tokens symbolTable = 
    let T2 = stmt tokens symbolTable
    let T3 = morestmts T2 symbolTable
    T3


  // commence to go through the main function to check
  let private simpleC tokens symboltable = 
    let T2 = matchToken "void" tokens
    let T3 = matchToken "main" T2
    let T4 = matchToken "(" T3
    let T5 = matchToken ")" T4
    let T6 = matchToken "{" T5
    let T7 = stmts    T6 symboltable
    let T8 = matchToken "}" T7
    let T9 = matchToken "$" T8  // $ => EOF, there should be no more tokens
    T9


  //
  // typecheck tokens symboltable
  //
  // Given a list of tokens and a symbol table, type-checks 
  // the program to ensure program's variables and expressions
  // are type-compatible. If the program is valid, returns 
  // the string "success". If the program contains a semantic
  // error or warning, returns a string of the form
  // "type_error: ...".
  //
  let typecheck tokens symboltable = 
    try
      let T2 = simpleC tokens symboltable
      "success"
    with 
      | ex -> "type_error: " + ex.Message