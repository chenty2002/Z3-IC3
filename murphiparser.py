from lark import Lark, Transformer, v_args

import murphi

grammar = r"""

    ?const_decl:CNAME ":" INT
    ?consts:"const" (const_decl ";")*                     -> consts



    ?type_constr:CNAME                                    -> var_type    
        | (INT |CNAME) ".."  (INT |CNAME)                 -> range_type	
        | "boolean"                                       -> boolean_type
        | "scalarset" "(" CNAME ")"                       -> scalarset_type
        | "union" "{" type_constr ("," type_constr)* "}"  -> union_type
        | "enum" "{" CNAME ("," CNAME)* "}"               -> enum_type
        | "array" "[" type_constr "]" "of" type_constr    -> array_type
        | "record" (type_decl ";")* "end"                 -> record_type

    ?type_decl: CNAME ":" type_constr
    ?types: "type" (type_decl ";")*                       -> types

    ?var_decl: CNAME ":" type_constr
    ?vars: "var" (var_decl ";")*                          -> vars

    ?atom_expr: CNAME                                     -> unknown_expr 
        | INT                                             -> int_expr
        | atom_expr "." CNAME                             -> field_name
        | atom_expr "[" expr "]"                          -> array_index
        | "forall" var_decl "do" expr ("end" | "endforall")               -> forall_expr
        | "exists" var_decl "do" expr "end"               -> exists_expr
        | "(" expr ")"

    ?neg_expr: "!" atom_expr                              -> neg_expr
        | atom_expr

    ?eq_expr: neg_expr "=" neg_expr                       -> eq_expr
        | neg_expr "!=" neg_expr                          -> ineq_expr
        | neg_expr

    ?and_expr: eq_expr "&" and_expr
        | eq_expr

    ?or_expr: and_expr "|" or_expr
        | and_expr

    ?imp_expr: or_expr "->" imp_expr
        | or_expr

    ?add_expr: imp_expr "+" add_expr
        | imp_expr

    ?sub_expr: add_expr "-" sub_expr
        | add_expr

    ?mul_expr: sub_expr "*" mul_expr
        | sub_expr

    ?div_expr: mul_expr "/" div_expr
        | mul_expr

    ?mod_expr: div_expr "%" mod_expr
        | div_expr

    ?smaller_expr: mod_expr "<=" smaller_expr
        | mod_expr

    ?larger_expr: smaller_expr ">" larger_expr
        | smaller_expr


    ?expr: larger_expr               

    ?cmd: "undefine" atom_expr                            -> undefine_cmd
        | atom_expr ":=" expr                             -> assign_cmd
        | "for" var_decl "do" cmds ("end" | "endfor")     -> forall_cmd
        | "if" expr "then" cmds ("elsif" expr "then" cmds)* ("else" cmds)? ("end" | "endif")  -> if_cmd

    ?cmds: (cmd ";")*                                     -> cmds

    ?startstate: "startstate" ESCAPED_STRING ("begin")? cmds "endstartstate" ";"

    ?var_decls: var_decl (";" var_decl)*                  -> var_decls

    ?rule: "rule" ESCAPED_STRING expr "==>" (vars)?  "begin" cmds "endrule" ";"

    ?ruleset: "ruleset" var_decls "do" (rule | startstate) "endruleset" ";"

    ?invariant: "invariant" ESCAPED_STRING expr ";"

    ?axiom_cmd: "axiom" ESCAPED_STRING expr ";"

    ?prot_decl: rule | ruleset | invariant | axiom_cmd

    ?rulesetstartstate: "ruleset" var_decls "do" startstate "endruleset" ";"

    ?startstate_decl: startstate | rulesetstartstate

    ?protocol: consts types vars startstate_decl (prot_decl)*

    COMMENT: "--" /[^\n]*/ NEWLINE

    %import common.NEWLINE
    %import common.CNAME
    %import common.WS
    %import common.INT
    %import common.ESCAPED_STRING
    %ignore WS
    %ignore COMMENT

"""


@v_args(inline=True)
class MurphiTransformer(Transformer):
    def __init__(self):
        super().__init__()

    def const_decl(self, name, val):
        return murphi.MurphiConstDecl(str(name), val)

    def consts(self, *decls):
        return decls

    def int_const_rng(self, val):
        return murphi.IntRngConst(int(val))

    def name_const_rng(self, name):
        return murphi.NameRngConst(name)

    def var_type(self, name):
        return murphi.VarType(str(name))

    def range_type(self, downRng, upRng):
        """
        if downRng.isdigit():
            downRng=int(downRng)
        if upRng.isdigit():
            upRng=int(upRng)
        """
        return murphi.RngType(str(downRng), str(upRng))

    def boolean_type(self):
        return murphi.BooleanType()

    def scalarset_type(self, const_name):
        return murphi.ScalarSetType(str(const_name))

    def union_type(self, *typs):
        return murphi.UnionType(typs)

    def enum_type(self, *names):
        return murphi.EnumType([str(name) for name in names])

    def array_type(self, idx_typ, ele_typ):
        return murphi.ArrayType(idx_typ, ele_typ)

    def record_type(self, *decls):
        return murphi.RecordType(decls)

    def type_decl(self, name, typ):
        return murphi.MurphiTypeDecl(str(name), typ)

    def types(self, *decls):
        return decls

    def var_decl(self, name, typ):
        return murphi.MurphiVarDecl(str(name), typ)

    def vars(self, *decls):
        return decls

    def unknown_expr(self, name):
        return murphi.UnknownExpr(str(name))

    def field_name(self, v, field):
        return murphi.FieldName(v, field)

    def array_index(self, v, idx):
        return murphi.ArrayIndex(v, idx)

    def forall_expr(self, decl, expr):
        return murphi.ForallExpr(decl, expr)

    def exists_expr(self, decl, expr):
        return murphi.ExistsExpr(decl, expr)

    def neg_expr(self, expr):
        return murphi.NegExpr(expr)

    def eq_expr(self, expr1, expr2):
        return murphi.OpExpr("=", expr1, expr2)

    def ineq_expr(self, expr1, expr2):
        return murphi.OpExpr("!=", expr1, expr2)

    def and_expr(self, expr1, expr2):
        return murphi.OpExpr("&", expr1, expr2)

    def or_expr(self, expr1, expr2):
        return murphi.OpExpr("|", expr1, expr2)

    def imp_expr(self, expr1, expr2):
        return murphi.OpExpr("->", expr1, expr2)

    def add_expr(self, expr1, expr2):
        return murphi.OpExpr("+", expr1, expr2)

    def sub_expr(self, expr1, expr2):
        return murphi.OpExpr("-", expr1, expr2)

    def mul_expr(self, expr1, expr2):
        return murphi.OpExpr("*", expr1, expr2)

    def int_expr(self, expr):
        return murphi.IntExpr(expr)

    def div_expr(self, expr1, expr2):
        return murphi.OpExpr("/", expr1, expr2)

    def mod_expr(self, expr1, expr2):
        return murphi.OpExpr("%", expr1, expr2)

    def smaller_expr(self, expr1, expr2):
        return murphi.OpExpr("<=", expr1, expr2)

    def larger_expr(self, expr1, expr2):
        return murphi.OpExpr(">", expr1, expr2)

    def axiom_cmd(self, name, expr):
        print("paser-axiom:", name, expr)
        return murphi.AxiomExpr(name, expr)

    def undefine_cmd(self, var):
        return murphi.UndefineCmd(var)

    def assign_cmd(self, var, expr):
        # print(expr)
        return murphi.AssignCmd(var, expr)

    def forall_cmd(self, var_decl, cmds):
        return murphi.ForallCmd(var_decl, cmds)

    def if_cmd(self, *args):
        return murphi.IfCmd(args)

    def cmds(self, *args):
        return args

    def startstate(self, name, cmds):
        return murphi.StartState(str(name[1:-1]), cmds)

    def rule(self, *args):
        return murphi.MurphiRule(args)

    def var_decls(self, *decls):
        return decls

    def ruleset(self, decls, rule):
        return murphi.MurphiRuleSet(decls, rule)

    def rulesetstartstate(self, decls, startstate):
        return murphi.RulesetStartState(decls, startstate)

    def invariant(self, name, inv):
        return murphi.MurphiInvariant(str(name[1:-1]), inv)

    def protocol(self, consts, types, vars, start_state, *decls):
        return murphi.MurphiProtocol(consts, types, vars, start_state, decls)


def parse_file(filename):
    murphi_parser = Lark(grammar, start="protocol", parser="lalr", transformer=MurphiTransformer())
    with open(filename, "r") as file:
        return murphi_parser.parse(file.read())


if __name__ == "__main__":
    parse_path = "protocols/mutualEx/"
    parse_name = "mutualEx"
    # prot = parse_file(parse_path+parse_name+".m", ivyselect, smvSelect)
    save = parse_path + parse_name + "_out.m"
    # print(prot)
    parser = Lark(grammar, start="protocol", parser="lalr", transformer=MurphiTransformer())
    with open(parse_path + parse_name + ".m", "r") as f:
        prot = parser.parse(f.read())
