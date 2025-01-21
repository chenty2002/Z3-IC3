import re
import lark


def indent(s, num_space, first_line=None):
    """
    Indent the given string by adding spaces to each line.

    Parameters
    ----------
    s : str
    num_space : int
        Number of spaces to add to each line
    first_line : int, optional
        Number of spaces to add to first line
    """
    lines = s.split('\n')
    if first_line is None:
        return '\n'.join(' ' * num_space + line for line in lines)
    else:
        res = ' ' * first_line + lines[0]
        if len(lines) > 1:
            res += '\n' + '\n'.join(' ' * num_space + line for line in lines[1:])
        return res


const_map = dict()
digitType_map = dict()
re_digitType_map = dict()
specific_typ = {}
specific_var = {}
specific_enum_var = {}


class MurphiConstDecl:
    def __init__(self, name, val):
        self.name = name
        self.val = val
        const_map[name] = val

    def __str__(self):
        return f'{self.name} : {self.val}'

    def __repr__(self):
        return f'MurphiConst({self.name}, {self.val})'

    def __eq__(self, other):
        return isinstance(other, MurphiConstDecl) and self.name == other.name and self.val == other.val


class MurphiType:
    pass


class VarType(MurphiType):
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name

    def __repr__(self):
        return f'VarType({self.name})'

    def __eq__(self, other):
        return isinstance(other, VarType) and self.name == other.name

    def __hash__(self):
        return hash(self.name)


class RngType(MurphiType):
    def __init__(self, down_rng: str, up_rng: str):
        self.downRng = down_rng
        self.upRng = up_rng

    def __str__(self):
        return f'{self.downRng}..{self.upRng}'

    def __repr__(self):
        return f'RangeType (is {self.downRng} .. {self.upRng})'

    def __eq__(self, other):
        return isinstance(other, RngType) and self.downRng == other.downRng and self.upRng == other.upRng

    def __hash__(self):
        return hash((self.downRng, self.upRng))


class BooleanType(MurphiType):
    def __init__(self):
        pass

    def __str__(self):
        return 'boolean'

    def __repr__(self):
        return 'BooleanType()'

    def __eq__(self, other):
        return isinstance(other, BooleanType)

    def __hash__(self):
        return hash('boolean')


class ScalarSetType(MurphiType):
    def __init__(self, const_name: str):
        assert isinstance(const_name, str)
        self.const_name = const_name

    def __str__(self):
        return f'scalarset({self.const_name})'

    def __repr__(self):
        return f'ScalarSetType({self.const_name})'

    def __eq__(self, other):
        return isinstance(other, ScalarSetType) and self.const_name == other.const_name

    def __hash__(self):
        return hash(self.const_name)


class UnionType(MurphiType):
    def __init__(self, typs):
        self.typs = typs

    def __str__(self):
        typs = ', '.join(str(typ) for typ in self.typs)
        return f'union {typs}'

    def __repr__(self):
        typs = ', '.join(repr(typ) for typ in self.typs)
        return f'UnionType({typs})'

    def __eq__(self, other):
        return isinstance(other, UnionType) and self.typs == other.typs

    def __hash__(self):
        return hash(tuple(self.typs))


class EnumType(MurphiType):
    def __init__(self, names):
        self.names = names

    def __str__(self):
        enums = ', '.join(name for name in self.names)
        return f'enum {enums}'

    def __repr__(self):
        enums = ', '.join(repr(name) for name in self.names)
        return f"EnumType({enums})"

    def __eq__(self, other):
        return isinstance(other, EnumType) and self.names == other.names

    def __hash__(self):
        return hash(tuple(self.names))


class ArrayType(MurphiType):
    def __init__(self, idx_typ, ele_typ):
        self.idx_typ = idx_typ
        self.ele_typ = ele_typ

    def __str__(self):
        return f'array [{self.idx_typ}] of {self.ele_typ}'

    def __repr__(self):
        return f'ArrayType({repr(self.idx_typ)}, {repr(self.ele_typ)}'

    def __eq__(self, other):
        return isinstance(other, ArrayType) and self.idx_typ == other.idx_typ and self.ele_typ == other.ele_typ

    def __hash__(self):
        return hash((self.idx_typ, self.ele_typ))


class RecordType(MurphiType):
    def __init__(self, typ_decls):
        self.typ_decls = typ_decls

    def __str__(self):
        decls = '\n'.join(indent(str(decl), 2) + ';' for decl in self.typ_decls)
        return f'record\n{decls}\nend'

    def __repr__(self):
        decls = ', '.join(repr(decl) for decl in self.typ_decls)
        return f'RecordType({decls})'

    def __eq__(self, other):
        return isinstance(other, RecordType) and self.typ_decls == other.typ_decls

    def __hash__(self):
        return hash(tuple(self.typ_decls))


union_dict = dict()


class MurphiTypeDecl:
    def __init__(self, name, typ):
        # specific_typ[str(name)] = typ
        self.name = name
        self.typ = typ
        if isinstance(self.typ, ScalarSetType):
            digitType_map[self.name] = self.typ
            re_digitType_map[self.typ.const_name] = self.name
        elif isinstance(self.typ, RngType):
            digitType_map[self.name] = self.typ
            re_digitType_map[str(self.typ)] = self.name

    def __str__(self):
        return f'{self.name} : {self.typ}'

    def __repr__(self):
        return f'MurphiTypeDecl({repr(self.name)}, {self.typ})'

    def __eq__(self, other):
        return isinstance(other, MurphiTypeDecl) and self.name == other.name and self.typ == other.typ


class MurphiVarDecl:
    def __init__(self, name, typ):
        self.name = name
        self.typ = typ

    def __str__(self):
        return f'{self.name} : {self.typ}'

    def __repr__(self):
        return f'MurphiVarDecl({repr(self.name)}, {self.typ})'

    def __eq__(self, other):
        return isinstance(other, MurphiVarDecl) and self.name == other.name and self.typ == other.typ


class BaseExpr:
    """Base class for Murphi expressions."""

    def priority(self) -> int:
        raise NotImplementedError

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType]) -> "BaseExpr":
        return self


class UnknownExpr(BaseExpr):
    def __init__(self, s):
        self.s = s

    def priority(self):
        return 100

    def __str__(self):
        return f'#{self.s}#'

    def __repr__(self):
        return f'UnknownExpr({self.s})'

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType]) -> BaseExpr:
        if self.s == 'true':
            return BooleanExpr(True)
        elif self.s == 'false':
            return BooleanExpr(False)
        elif self.s in prot.enum_map:
            return EnumValExpr(prot.enum_map[self.s], self.s)
        elif self.s in bound_vars:
            return VarExpr(self.s, bound_vars[self.s])
        elif self.s in prot.var_map:
            return VarExpr(self.s, prot.var_map[self.s])
        else:
            return VarExpr(self.s, prot.var_map[self.s])


class BooleanExpr(BaseExpr):
    def __init__(self, val):
        self.val = val

    def priority(self):
        return 100

    def __str__(self):
        return str(self.val)

    def __repr__(self):
        return f'BooleanExpr({repr(self.val)})'

    def __eq__(self, other):
        return isinstance(other, BooleanExpr) and self.val == other.val

    def elaborate(self, prot, bound_vars):
        return self


class EnumValExpr(BaseExpr):
    def __init__(self, enum_type, enum_val):
        self.enum_type = enum_type
        self.enum_val = enum_val

    def priority(self):
        return 100

    def __str__(self):
        return self.enum_val

    def __repr__(self):
        return f'EnumValExpr({repr(self.enum_type)}, {repr(self.enum_val)})'

    def __eq__(self, other):
        return isinstance(other, EnumValExpr) and self.enum_type == other.enum_type and self.enum_val == other.enum_val

    def elaborate(self, prot, bound_vars):
        return self


class VarExpr(BaseExpr):
    def __init__(self, name, typ):
        self.name = name
        self.typ = typ

    def priority(self):
        return 100

    def __str__(self):
        return str(self.name)

    def __repr__(self):
        return f'VarExpr({repr(self.name)})'

    def __eq__(self, other):
        return isinstance(other, VarExpr) and self.name == other.name and self.typ == other.typ

    def elaborate(self, prot, bound_vars):
        return self


class FieldName(BaseExpr):
    def __init__(self, v: BaseExpr, field: str):
        self.v = v
        self.field = field

    def priority(self):
        return 100

    def __str__(self):
        return f'{self.v}.{self.field}'

    def __repr__(self):
        return f'FieldName({repr(self.v)}, {repr(self.field)})'

    def __eq__(self, other):
        return isinstance(other, FieldName) and self.v == other.v and self.field == other.field

    def elaborate(self, prot, bound_vars):
        return FieldName(self.v.elaborate(prot, bound_vars), self.field)


class ArrayIndex(BaseExpr):
    def __init__(self, v: BaseExpr, idx: BaseExpr):
        self.v = v
        self.idx = idx

    def priority(self):
        return 100

    def __str__(self):
        return f'{self.v}[{self.idx}]'

    def __repr__(self):
        return f'ArrayIndex({repr(self.v)}, {repr(self.idx)})'

    def __eq__(self, other):
        return isinstance(other, ArrayIndex) and self.v == other.v and self.idx == other.idx

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType]) -> BaseExpr:
        return ArrayIndex(self.v.elaborate(prot, bound_vars), self.idx.elaborate(prot, bound_vars))


invVars = dict()


class ForallExpr(BaseExpr):
    def __init__(self, var_decl: MurphiVarDecl, expr: BaseExpr):
        self.var_decl = var_decl
        self.var, self.typ = self.var_decl.name, self.var_decl.typ
        self.expr = expr

    def priority(self):
        return 70

    def __str__(self):
        return f'forall {self.var_decl} do\n{indent(str(self.expr), 2)}\nend'

    def __repr__(self):
        return f'ForallExpr({repr(self.var_decl)}, {repr(self.expr)})'

    def __eq__(self, other):
        return isinstance(other, ForallExpr) and self.var_decl == other.var_decl and self.expr == other.expr

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType]) -> BaseExpr:
        bound_vars[self.var] = self.typ
        res = ForallExpr(self.var_decl, self.expr.elaborate(prot, bound_vars))
        del bound_vars[self.var]
        return res


class ExistsExpr(BaseExpr):
    def __init__(self, var_decl, expr):
        self.var_decl = var_decl
        self.var, self.typ = self.var_decl.name, self.var_decl.typ
        self.expr = expr

    def priority(self):
        return 70

    def __str__(self):
        res = f'exists {self.var_decl} do {self.expr} end'
        return res

    def __repr__(self):
        return f'ExistsExpr({repr(self.var_decl)}, {repr(self.expr)})'

    def __eq__(self, other):
        return isinstance(other, ExistsExpr) and self.var_decl == other.var_decl and self.expr == other.expr

    def elaborate(self, prot, bound_vars):
        bound_vars[self.var] = self.typ
        res = ExistsExpr(self.var_decl, self.expr.elaborate(prot, bound_vars))
        del bound_vars[self.var]
        return res


priority_map = {
    '*': 65,
    '/': 65,
    '%': 65,
    '<=': 62,
    '>=': 62,
    '<': 62,
    '>': 62,
    '+': 60,
    '-': 60,
    '=': 50,
    '!=': 50,
    '&': 35,
    '|': 30,
    '->': 25
}


class OpExpr(BaseExpr):
    def __init__(self, op: str, expr1: BaseExpr, expr2: BaseExpr):
        self.op = op
        self.expr1 = expr1
        self.expr2 = expr2

    def priority(self):
        return priority_map[self.op]

    def __str__(self):
        s1, s2 = str(self.expr1), str(self.expr2)
        global specific_var
        if self.op in ('&', '|', '->'):
            if not (isinstance(self.expr1, OpExpr)):
                if isinstance(self.expr1, NegExpr):
                    negvar_pt = re.sub(r'\[.*?\]', '[_]', str(self.expr1.expr))
                    if (str(self.expr1.expr) in specific_var.keys() and
                        isinstance(specific_var[str(self.expr1.expr)], BooleanType)) or \
                            (negvar_pt in specific_var.keys() and isinstance(specific_var[negvar_pt], BooleanType)):
                        self.expr1 = OpExpr('=', self.expr1.expr, BooleanExpr(False))
                        s1 = str(self.expr1)
                else:
                    var_pt = re.sub(r'\[.*?\]', '[_]', str(self.expr1))
                    if (str(self.expr1) in specific_var.keys() and
                        isinstance(specific_var[str(self.expr1)], BooleanType)) or \
                            (var_pt in specific_var.keys() and isinstance(specific_var[var_pt], BooleanType)):
                        self.expr1 = OpExpr('=', self.expr1, BooleanExpr(True))
                        s1 = str(self.expr1)
            if not (isinstance(self.expr2, OpExpr)):
                if isinstance(self.expr2, NegExpr):
                    negvar_pt = re.sub(r'\[.*?\]', '[_]', str(self.expr2.expr))
                    if (str(self.expr2.expr) in specific_var.keys() and
                        isinstance(specific_var[str(self.expr2.expr)], BooleanType)) or \
                            (negvar_pt in specific_var.keys() and isinstance(specific_var[negvar_pt], BooleanType)):
                        self.expr2 = OpExpr('=', self.expr2.expr, BooleanExpr(False))
                        s2 = str(self.expr2)
                else:
                    var_pt = re.sub(r'\[.*?\]', '[_]', str(self.expr2))
                    if (str(self.expr2) in specific_var.keys() and
                        isinstance(specific_var[str(self.expr2)], BooleanType)) or \
                            (var_pt in specific_var.keys() and isinstance(specific_var[var_pt], BooleanType)):
                        self.expr2 = OpExpr('=', self.expr2, BooleanExpr(True))
                        s2 = str(self.expr2)

        if self.expr1.priority() <= self.priority():
            if '\n' in s1:
                s1 = '(' + indent(s1, 2, first_line=1) + ' )'
            else:
                s1 = '(' + s1 + ')'
        if self.expr2.priority() < self.priority():
            if '\n' in s2:
                s2 = '(' + indent(s2, 2, first_line=1) + ' )'
            else:
                s2 = '(' + s2 + ')'
        if self.op in ('=', '+', '-', '*', '/', '<=', '>=', '>', '<', '%', '!=', '&', '|'):
            return '%s %s %s' % (s1, self.op, s2)
        elif self.op in '->':
            if isinstance(self.expr2, OpExpr) and self.expr2.op == '->':
                return '(%s) -> (%s)' % (s1, indent(s2, 2))
            else:
                return '(%s) -> %s' % (s1, indent(s2, 2))
        else:
            raise NotImplementedError

    def getVars(self):
        print(self.expr1, self.expr2)

    def __repr__(self):
        return f'OpExpr({self.op}, {self.expr1}, {self.expr2})'

    def __eq__(self, other):
        return isinstance(other, OpExpr) and self.op == other.op and self.expr1 == other.expr1 and \
               self.expr2 == other.expr2

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType]) -> BaseExpr:
        return OpExpr(self.op, self.expr1.elaborate(prot, bound_vars), self.expr2.elaborate(prot, bound_vars))


class IntExpr(BaseExpr):
    def __init__(self, expr):
        self.expr = expr

    def priority(self):
        return 80

    def __str__(self):
        s = str(self.expr)
        return s

    def __eq__(self, other):
        return isinstance(other, IntExpr) and self.expr == other.expr

    def __repr__(self):
        return f'INT({self.expr})'

    def elaborate(self, prot, bound_vars):
        return IntExpr(self.expr)


class NegExpr(BaseExpr):
    def __init__(self, expr: BaseExpr):
        self.expr = expr

    def priority(self):
        return 80

    def __str__(self):
        s = str(self.expr)
        if self.expr.priority() < self.priority():
            s = f'({s})'

        return f'!{s}'

    def __repr__(self):
        return f'NegExpr({self.expr})'

    def __eq__(self, other):
        return isinstance(other, NegExpr) and self.expr == other.expr

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType]) -> BaseExpr:
        return NegExpr(self.expr.elaborate(prot, bound_vars))


class BaseCmd:
    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType]) -> "BaseCmd":
        return self


class UndefineCmd(BaseCmd):
    def __init__(self, var):
        self.var = var

    def __str__(self):
        return f'undefine {self.var};'

    def __repr__(self):
        return f'UndefineCmd({self.var})'

    def __eq__(self, other):
        return isinstance(other, UndefineCmd) and self.var == other.var

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType]) -> "BaseCmd":
        return UndefineCmd(self.var.elaborate(prot, bound_vars))


datas = dict()
equal_datas = dict()


class AssignCmd(BaseCmd):
    def __init__(self, var, expr):
        assert isinstance(var, BaseExpr)
        # print(record_map)
        self.var = var
        self.expr = expr

    def __str__(self):
        return indent(f'{self.var} := {self.expr};\n', 0)

    def __repr__(self):
        return f'AssignCmd({self.var}, {self.expr})'

    def __eq__(self, other):
        return isinstance(other, AssignCmd) and self.var == other.var and self.expr == other.expr

    def elaborate(self, prot, bound_vars):
        if isinstance(self.expr, lark.lexer.Token):
            return AssignCmd(self.var.elaborate(prot, bound_vars), self.expr)
        return AssignCmd(self.var.elaborate(prot, bound_vars), self.expr.elaborate(prot, bound_vars))


def paraDataVars(equal_vars):
    cmds = set()
    equal_vars = set(equal_vars)
    for i in range(len(equal_vars) - 1, 0, -1):
        cmds.add(f"{list(equal_vars)[i]} := {list(equal_vars)[i - 1]}")
    return cmds


class ForallCmd(BaseCmd):
    def __init__(self, var_decl, cmds):
        self.var_decl = var_decl
        self.var, self.typ = self.var_decl.name, self.var_decl.typ
        self.cmds = cmds

    def __str__(self):
        res = f'for {self.var_decl} do\n'
        res += ''.join(indent(str(cmd), 2) + '\n' for cmd in self.cmds)
        res += 'end;'
        return res

    def __repr__(self):
        return f'ForallCmd({self.var_decl}, {self.cmds})'

    def __eq__(self, other):
        return isinstance(other, ForallCmd) and self.var_decl == other.var_decl and self.cmds == other.cmds

    def elaborate(self, prot, bound_vars):
        bound_vars[self.var] = self.typ
        res = ForallCmd(self.var_decl, [cmd.elaborate(prot, bound_vars) for cmd in self.cmds])
        del bound_vars[self.var]
        return res


class IfCmd(BaseCmd):
    def __init__(self, args):
        assert len(args) > 1
        self.args = args
        self.if_branches = list(zip(args[::2], args[1::2]))
        self.else_branch = args[-1] if len(args) % 2 == 1 else None

    def __str__(self):
        res = f'if ({self.if_branches[0][0]}) then\n'
        res += ''.join(indent(str(cmd), 2) + '\n' for cmd in self.if_branches[0][1])
        for expr, cmds in self.if_branches[1:]:
            res += f'elsif ({expr}) then\n'
            res += ''.join(indent(str(cmd), 2) + '\n' for cmd in cmds)
        if self.else_branch:
            res += 'else\n'
            res += ''.join(indent(str(cmd), 2) + '\n' for cmd in self.else_branch)
        res += 'end;'
        return res

    def __repr__(self):
        return f'IfCmd({self.args})'

    def __eq__(self, other):
        return isinstance(other, IfCmd) and self.args == other.args

    def elaborate(self, prot, bound_vars):
        new_args = []
        for arg in self.args:
            if isinstance(arg, BaseExpr):
                new_args.append(arg.elaborate(prot, bound_vars))
            else:
                new_args.append([cmd.elaborate(prot, bound_vars) for cmd in arg])
        return IfCmd(new_args)


class ProtDecl:
    def __init__(self, is_startstate):
        self.is_startstate = is_startstate

    def elaborate(self, prot, bound_vars):
        pass


class StartState(ProtDecl):
    def __init__(self, args):
        super().__init__(True)
        assert len(args) < 3
        if len(args) == 1:
            self.name = '__init__'
            self.cmds = args[0]
        else:
            self.name, self.cmds = args

    def __str__(self):
        res = f'startstate "{self.name}"\n'
        res += ''.join(indent(str(cmd), 2) + '\n' for cmd in self.cmds)
        res += 'endstartstate;'
        return res

    def __repr__(self):
        cmds_repr = ''.join(indent(str(cmd), 2) + '\n' for cmd in self.cmds)
        return f'StartState({self.name}, {cmds_repr})'

    def elaborate(self, prot, bound_vars):
        return StartState([self.name, [cmd.elaborate(prot, bound_vars) for cmd in self.cmds]])


class MurphiRule(ProtDecl):
    def __init__(self, args):
        super().__init__(False)
        self.rule_var_map = dict()
        self.args = args
        assert len(args) > 2
        if len(args) == 3:
            self.name, self.cond, self.cmds = args
        else:
            self.name, self.cond, self.rule_vars, self.cmds = args

            for rule_var in self.rule_vars:
                self.rule_var_map[rule_var.name] = rule_var.typ
        self.name = self.name.replace('"', '')

    def __str__(self):
        res = f'rule "{self.name}"\n'
        res += indent(str(self.cond), 2) + '\n'
        res += '==>\nbegin\n'
        res += ''.join(indent(str(cmd), 2) + '\n' for cmd in self.cmds)
        res += 'endrule;'
        return res

    def __repr__(self):
        return f'MurphiRule({self.name}, {self.cond}, {self.cmds})'

    def __eq__(self, other):
        return isinstance(other, MurphiRule) and self.name == other.name and self.cond == other.cond and self.cmds == other.cmds

    def elaborate(self, prot, bound_vars):
        new_args = [
            self.name,
            self.cond.elaborate(prot, bound_vars),
            [cmd.elaborate(prot, bound_vars) for cmd in self.cmds]
        ]
        if len(self.args) > 3:
            for var, typ in self.rule_var_map.items():
                bound_vars[var] = typ
            new_args.insert(2, self.rule_vars)
            for var in self.rule_var_map:
                del bound_vars[var]
        return MurphiRule(new_args)

    def addSpecialGuard(self, f):
        self.cond = OpExpr("&", f, self.cond)


class MurphiInvariant(ProtDecl):
    def __init__(self, name, inv):
        super().__init__(False)
        self.name = name
        self.inv = inv

    def __str__(self):
        res = "invariant \"%s\"\n" % self.name
        res += indent(str(self.inv), 2)
        res += ";\n"
        return res

    def __repr__(self):
        return "Invariant(%s, %s)" % (repr(self.name), repr(self.inv))

    def __eq__(self, other):
        return isinstance(other, MurphiInvariant) and self.name == other.name and \
               self.inv == other.inv

    def elaborate(self, prot, bound_vars):
        return MurphiInvariant(self.name, self.inv.elaborate(prot, bound_vars))


class MurphiRuleSet(ProtDecl):
    def __init__(self, var_decls: list[MurphiVarDecl], rules: list[MurphiRule | MurphiInvariant | StartState]):
        super().__init__(True in [isinstance(rule, StartState) for rule in rules])
        self.var_decls = var_decls
        self.var_map = dict()
        for var_decl in self.var_decls:
            self.var_map[var_decl.name] = var_decl.typ
        self.rules = rules

    def __str__(self):
        decls = '; '.join(str(decl) for decl in self.var_decls)
        res = f'ruleset {decls} do\n'
        res += '\n'.join(str(rule) for rule in self.rules)
        res += '\nendruleset;'
        return res

    def __repr__(self):
        rules = '\n'.join(repr(rule) for rule in self.rules)
        return f'MurphiRuleSet({self.var_decls}, {rules})'

    def elaborate(self, prot, bound_vars):
        for var, typ in self.var_map.items():
            bound_vars[var] = typ
        res = MurphiRuleSet(self.var_decls, [rule.elaborate(prot, bound_vars) for rule in self.rules])
        for var in self.var_map:
            del bound_vars[var]
        return res


class MurphiProtocol:
    def __init__(self,
                 consts: list[MurphiConstDecl],
                 types: list[MurphiTypeDecl],
                 vars: list[MurphiVarDecl],
                 decls: list[ProtDecl]):
        self.consts = consts
        self.types = types
        self.vars = vars
        self.decls = decls

        self.typ_map = dict()
        self.enum_typ_map = dict()
        self.enum_map = dict()
        self.scalarset = list()
        # Process types
        for typ_decl in self.types:
            self.typ_map[typ_decl.name] = typ_decl.typ
            if isinstance(typ_decl.typ, EnumType):
                self.enum_typ_map[typ_decl.name] = typ_decl.typ
                for enum_val in typ_decl.typ.names:
                    self.enum_map[enum_val] = typ_decl.typ

            if isinstance(typ_decl.typ, ScalarSetType):
                self.scalarset.append(typ_decl.name)

        # Process variables
        self.var_map = dict()
        for var_decl in self.vars:
            self.var_map[var_decl.name] = var_decl.typ

        # Elaboration
        self.decls = [decl.elaborate(self, dict()) for decl in self.decls]
        start_states = list(filter(lambda decl: decl.is_startstate, self.decls))
        assert len(start_states) == 1
        self.start_state = start_states[0]

        # Divide into categories
        self.rule_map = dict()
        self.inv_map = dict()

        for decl in self.decls:
            if isinstance(decl, MurphiRule):
                self.rule_map[decl.name] = decl
            elif isinstance(decl, MurphiRuleSet):
                for rule in decl.rules:
                    if isinstance(rule, MurphiRule):
                        self.rule_map[rule.name] = rule
                    elif isinstance(rule, MurphiInvariant):
                        self.inv_map[rule.name] = rule
            elif isinstance(decl, StartState):
                pass
            elif isinstance(decl, MurphiInvariant):
                self.inv_map[decl.name] = decl
            else:
                raise NotImplementedError
        # refine abs_r_src etc
        self.export_name = list(self.rule_map.keys())

    def __str__(self):
        consts_str = '\n\n'.join(indent(str(const), 2) + ';' for const in self.consts)
        types_str = '\n\n'.join(indent(str(typ), 2) + ';' for typ in self.types)
        vars_str = '\n\n'.join(indent(str(var), 2) + ';' for var in self.vars)
        decls_str = '\n\n'.join(str(decl) for decl in self.decls)
        res = (f'const\n\n{consts_str}\n\n'
               f'type\n\n{types_str}\n\n'
               f'var\n\n{vars_str}\n\n'
               f'{str(self.start_state)}\n\n'
               f'{decls_str}\n\n')
        return res

    def __repr__(self):
        return "MurphiProtocol(%s, %s, %s, %s, %s)" % (
            repr(self.consts), repr(self.types), repr(self.vars), repr(self.start_state), repr(self.decls))
