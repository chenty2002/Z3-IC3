from lark import Lark, Transformer, v_args

import murphi


@v_args(inline=True)
class MurphiTransformer(Transformer):
    def __init__(self):
        super().__init__()

    def const_decl(self, name, val):
        return murphi.MurphiConstDecl(str(name), int(val))

    def consts(self, *decls):
        return decls

    def var_type(self, name):
        return murphi.VarType(str(name))

    def range_type(self, downRng, upRng):
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
        return murphi.OpExpr('=', expr1, expr2)

    def ineq_expr(self, expr1, expr2):
        return murphi.OpExpr('!=', expr1, expr2)

    def and_expr(self, expr1, expr2):
        return murphi.OpExpr('&', expr1, expr2)

    def or_expr(self, expr1, expr2):
        return murphi.OpExpr('|', expr1, expr2)

    def imp_expr(self, expr1, expr2):
        return murphi.OpExpr('->', expr1, expr2)

    def add_expr(self, expr1, expr2):
        return murphi.OpExpr('+', expr1, expr2)

    def sub_expr(self, expr1, expr2):
        return murphi.OpExpr('-', expr1, expr2)

    def mul_expr(self, expr1, expr2):
        return murphi.OpExpr('*', expr1, expr2)

    def int_expr(self, expr):
        return murphi.IntExpr(int(expr))

    def div_expr(self, expr1, expr2):
        return murphi.OpExpr('/', expr1, expr2)

    def mod_expr(self, expr1, expr2):
        return murphi.OpExpr('%', expr1, expr2)

    def smaller_expr(self, expr1, expr2):
        return murphi.OpExpr('<=', expr1, expr2)

    def larger_expr(self, expr1, expr2):
        return murphi.OpExpr('>', expr1, expr2)

    def undefine_cmd(self, var):
        return murphi.UndefineCmd(var)

    def assign_cmd(self, var, expr):
        return murphi.AssignCmd(var, expr)

    def forall_cmd(self, var_decl, cmds):
        return murphi.ForallCmd(var_decl, cmds)

    def if_cmd(self, *args):
        return murphi.IfCmd(args)

    def cmds(self, *args):
        return args

    def startstate(self, *args):
        return murphi.StartState(args)

    def rule(self, *args):
        return murphi.MurphiRule(args)

    def var_decls(self, *decls):
        return decls

    def ruleset(self, decls, *rules):
        return murphi.MurphiRuleSet(decls, rules)

    def invariant(self, name, inv):
        return murphi.MurphiInvariant(str(name[1:-1]), inv)

    def protocol(self, consts, types, vars, *decls):
        return murphi.MurphiProtocol(consts, types, vars, decls)


def parse_file(filename):
    with open("grammar.lark", "r") as file_lark:
        grammar = file_lark.read()
        murphi_parser = Lark(grammar, start='protocol', parser='lalr', transformer=MurphiTransformer())
        with open(filename, 'r') as file:
            return murphi_parser.parse(file.read())


if __name__ == '__main__':
    file_name = "mutualEx.m"
    # prot = parse_file(parse_path+parse_name+'.m', ivyselect, smvSelect)
    lex_tree = parse_file(file_name)
    print(lex_tree)
