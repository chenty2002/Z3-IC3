import re
from typing import Optional, Callable
from z3 import *
from operator import add, sub, mul, truediv, mod, eq, ne, le, ge, lt, gt


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
    def __init__(self, z3_type=None):
        self.z3_type: Optional[DatatypeSortRef | range | int | bool] = z3_type

    def elaborate(self, prot: "MurphiProtocol", **kwargs):
        raise NotImplementedError


class VarType(MurphiType):
    __instances = dict()

    def __new__(cls, *args, **kwargs):
        idx = args[0]
        if idx not in cls.__instances:
            cls.__instances[idx] = super().__new__(cls)
        return cls.__instances[idx]

    def __init__(self, name):
        super().__init__()
        self.name = name

    def __str__(self):
        return self.name

    def __repr__(self):
        return f'VarType({self.name})'

    def __eq__(self, other):
        return isinstance(other, VarType) and self.name == other.name

    def __hash__(self):
        return hash(self.name)

    def elaborate(self, prot: "MurphiProtocol", **kwargs):
        if self.name in prot.var_map:
            self.z3_type = prot.var_map[self.name].z3_type
        elif self.name in prot.typ_map:
            self.z3_type = prot.typ_map[self.name].z3_type
        else:
            raise ValueError(f'Variable {self.name} not declared')


class RngType(MurphiType):
    __instances = dict()

    def __new__(cls, *args, **kwargs):
        idx = tuple(args[:2])
        if idx not in cls.__instances:
            cls.__instances[idx] = super().__new__(cls)
        return cls.__instances[idx]

    def __init__(self, down_rng: str, up_rng: str):
        super().__init__()
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

    def elaborate(self, prot: "MurphiProtocol", **kwargs):
        down_str = self.downRng
        for name, val in const_map.items():
            down_str = down_str.replace(name, str(val))
        down: int = eval(down_str)
        up_str = self.upRng
        for name, val in const_map.items():
            up_str = up_str.replace(name, str(val))
        up: int = eval(up_str)
        self.z3_type = range(down, up + 1)


class BooleanType(MurphiType):
    __instance = None

    def __new__(cls, *args, **kwargs):
        if cls.__instance is None:
            cls.__instance = super().__new__(cls)
        return cls.__instance

    def __init__(self):
        super().__init__(BoolSort())

    def __str__(self):
        return 'boolean'

    def __repr__(self):
        return 'BooleanType()'

    def __eq__(self, other):
        return isinstance(other, BooleanType)

    def __hash__(self):
        return hash('boolean')

    def elaborate(self, prot: "MurphiProtocol", **kwargs):
        return


class ScalarSetType(MurphiType):
    __instances = dict()

    def __new__(cls, *args, **kwargs):
        idx = args[0]
        if idx not in cls.__instances:
            cls.__instances[idx] = super().__new__(cls)
        return cls.__instances[idx]

    def __init__(self, const_name: str):
        super().__init__()
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
    __instances = dict()

    def __new__(cls, *args, **kwargs):
        idx = tuple(args)
        if idx not in cls.__instances:
            cls.__instances[idx] = super().__new__(cls)
        return cls.__instances[idx]

    def __init__(self, typs):
        super().__init__()
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
    __instances = dict()

    def __new__(cls, *args, **kwargs):
        idx = tuple(args[0])
        if idx not in cls.__instances:
            cls.__instances[idx] = super().__new__(cls)
        return cls.__instances[idx]

    def __init__(self, names):
        super().__init__()
        self.names = names
        self.enum_map: dict[str, DatatypeRef] = {}

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

    def elaborate(self, prot: "MurphiProtocol", **kwargs):
        self.z3_type, enum_val = EnumSort(kwargs['typ_name'], self.names)
        self.enum_map = {name: val for name, val in zip(self.names, enum_val)}


class ArrayType(MurphiType):
    __instances = dict()

    def __new__(cls, *args, **kwargs):
        idx = tuple(args[:2])
        if idx not in cls.__instances:
            cls.__instances[idx] = super().__new__(cls)
        return cls.__instances[idx]

    def __init__(self, idx_typ, ele_typ):
        super().__init__()
        self.ele_z3_type: Optional[DatatypeSortRef] = None
        self.idx_z3_type: Optional[DatatypeSortRef] = None
        self.idx_typ: MurphiType = idx_typ
        self.ele_typ: MurphiType = ele_typ

    def __str__(self):
        return f'array [{self.idx_typ}] of {self.ele_typ}'

    def __repr__(self):
        return f'ArrayType({repr(self.idx_typ)}, {repr(self.ele_typ)}'

    def __eq__(self, other):
        return isinstance(other, ArrayType) and self.idx_typ == other.idx_typ and self.ele_typ == other.ele_typ

    def __hash__(self):
        return hash((self.idx_typ, self.ele_typ))

    def elaborate(self, prot: "MurphiProtocol", **kwargs):
        self.idx_typ.elaborate(prot, **kwargs)
        self.ele_typ.elaborate(prot, **kwargs)
        self.idx_z3_type: range = self.idx_typ.z3_type
        self.ele_z3_type = self.ele_typ.z3_type
        self.z3_type = self.ele_z3_type


class RecordType(MurphiType):
    __instances = dict()

    def __new__(cls, *args, **kwargs):
        idx = tuple(args)
        if idx not in cls.__instances:
            cls.__instances[idx] = super().__new__(cls)
        return cls.__instances[idx]

    def __init__(self, typ_decls):
        super().__init__()
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
        self.typ: MurphiType = typ
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

    def elaborate(self, prot: "MurphiProtocol"):
        self.typ.elaborate(prot, typ_name=self.name)


class MurphiVarDecl:
    def __init__(self, name, typ):
        self.name = name
        self.typ: MurphiType = typ
        self.z3_expr: Optional[DatatypeRef] = None

    def __str__(self):
        return f'{self.name} : {self.typ}'

    def __repr__(self):
        return f'MurphiVarDecl({repr(self.name)}, {self.typ})'

    def __eq__(self, other):
        return isinstance(other, MurphiVarDecl) and self.name == other.name and self.typ == other.typ

    def elaborate(self, prot: "MurphiProtocol"):
        self.typ.elaborate(prot, typ_name=self.name)
        if isinstance(self.typ, ArrayType):
            assert isinstance(self.typ.idx_z3_type, range)
            self.z3_expr = [Const(f'{self.name}[{i}]', self.typ.ele_z3_type) for i in self.typ.idx_z3_type]
        else:
            self.z3_expr = Const(self.name, self.typ.z3_type)


class BaseExpr:
    """Base class for Murphi expressions."""

    def __init__(self, z3_expr=None):
        self.z3_expr: Optional[DatatypeRef] = z3_expr

    def priority(self) -> int:
        raise NotImplementedError

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], is_prime=True) -> "BaseExpr":
        return self


class UnknownExpr(BaseExpr):
    def __init__(self, s):
        super().__init__()
        self.s = s

    def priority(self):
        return 100

    def __str__(self):
        return f'#{self.s}#'

    def __repr__(self):
        return f'UnknownExpr({self.s})'

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], is_prime=True) -> BaseExpr:
        if self.s == 'true':
            expr = BooleanExpr(True)
        elif self.s == 'false':
            expr = BooleanExpr(False)
        elif self.s in prot.enum_map:
            expr = EnumValExpr(prot.enum_map[self.s], self.s)
        elif self.s in bound_vars:
            expr = VarExpr(self.s, bound_vars[self.s])
        else:
            expr = VarExpr(self.s, prot.var_map[self.s])
        return expr.elaborate(prot, bound_vars, is_prime)


class BooleanExpr(BaseExpr):
    def __init__(self, val):
        super().__init__(BoolVal(val))
        self.val = val

    def priority(self):
        return 100

    def __str__(self):
        return str(self.val)

    def __repr__(self):
        return f'BooleanExpr({repr(self.val)})'

    def __eq__(self, other):
        return isinstance(other, BooleanExpr) and self.val == other.val

    def elaborate(self, prot, bound_vars, is_prime=True):
        return self


class EnumValExpr(BaseExpr):
    def __init__(self, enum_type, enum_val):
        super().__init__(enum_type.enum_map[enum_val])
        self.enum_type: EnumType = enum_type
        self.enum_val: str = enum_val

    def priority(self):
        return 100

    def __str__(self):
        return self.enum_val

    def __repr__(self):
        return f'EnumValExpr({repr(self.enum_type)}, {repr(self.enum_val)})'

    def __eq__(self, other):
        return isinstance(other, EnumValExpr) and self.enum_type == other.enum_type and self.enum_val == other.enum_val

    def elaborate(self, prot, bound_vars, is_prime=True):
        return self


class VarExpr(BaseExpr):
    def __init__(self, name, typ):
        super().__init__()
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

    def elaborate(self, prot, bound_vars, is_prime=True):
        if self.name in bound_vars:
            self.z3_expr = bound_vars[self.name].z3_type
        else:
            if is_prime:
                self.z3_expr = prot.var_z3_map_prime[self.name + '\'']
            else:
                self.z3_expr = prot.var_z3_map[self.name]
        return self


class FieldName(BaseExpr):
    def __init__(self, v: BaseExpr, field: str):
        super().__init__()
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

    def elaborate(self, prot, bound_vars, is_prime=True):
        self.v = self.v.elaborate(prot, bound_vars, is_prime)
        return self


class ArrayIndex(BaseExpr):
    def __init__(self, v: BaseExpr, idx: BaseExpr):
        super().__init__()
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

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], is_prime=True) -> BaseExpr:
        self.v = self.v.elaborate(prot, bound_vars, is_prime)
        self.idx = self.idx.elaborate(prot, bound_vars, is_prime=False)
        if bound_vars:
            if isinstance(self.v, VarExpr) and isinstance(self.v.typ, ArrayType) and isinstance(self.idx.z3_expr, range):
                self.z3_expr = self.v.z3_expr
            else:
                raise ValueError('Array index error')
        return self


invVars = dict()


class ForallExpr(BaseExpr):
    def __init__(self, var_decl: MurphiVarDecl, expr: BaseExpr):
        super().__init__()
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

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], is_prime=True) -> BaseExpr:
        var_name = f'{self.var}\'' if is_prime else self.var
        self.expr = self.expr.elaborate(prot, bound_vars | {var_name: self.typ}, is_prime)
        return self


class ExistsExpr(BaseExpr):
    def __init__(self, var_decl, expr):
        super().__init__()
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

    def elaborate(self, prot, bound_vars, is_prime=True):
        self.expr = self.expr.elaborate(prot, bound_vars | {self.var: self.typ}, is_prime)
        return self


priority_map: dict[str, int] = {
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

operator_map: dict[str, Callable[[AstRef, AstRef], AstRef]] = {
    '*': mul,
    '/': truediv,
    '%': mod,
    '+': add,
    '-': sub,
    '=': eq,
    '<=': le,
    '>=': ge,
    '>': gt,
    '<': lt,
    '!=': ne,
    '&': And,
    '|': Or,
    '->': Implies
}


def expr2str(expr: BaseExpr):
    if not (isinstance(expr, OpExpr)):
        if isinstance(expr, NegExpr):
            negvar_pt = re.sub(r'\[.*?]', '[_]', str(expr.expr))
            if (str(expr.expr) in specific_var.keys() and
                isinstance(specific_var[str(expr.expr)], BooleanType)) or \
                    (negvar_pt in specific_var.keys() and isinstance(specific_var[negvar_pt], BooleanType)):
                expr = OpExpr('=', expr.expr, BooleanExpr(False))
                return str(expr)
        else:
            var_pt = re.sub(r'\[.*?]', '[_]', str(expr))
            if (str(expr) in specific_var.keys() and
                isinstance(specific_var[str(expr)], BooleanType)) or \
                    (var_pt in specific_var.keys() and isinstance(specific_var[var_pt], BooleanType)):
                expr = OpExpr('=', expr, BooleanExpr(True))
                return str(expr)


class OpExpr(BaseExpr):
    def __init__(self, op: str, expr1: BaseExpr, expr2: BaseExpr):
        super().__init__()
        self.op = op
        self.expr1 = expr1
        self.expr2 = expr2

    def priority(self):
        return priority_map[self.op]

    def __str__(self):
        s1, s2 = str(self.expr1), str(self.expr2)
        global specific_var
        if self.op in ('&', '|', '->'):
            s1 = expr2str(self.expr1)
            s2 = expr2str(self.expr2)

        if self.expr1.priority() <= self.priority():
            if '\n' in s1:
                s1 = f'({indent(s1, 2, first_line=1)})'
            else:
                s1 = f'({s1})'
        if self.expr2.priority() < self.priority():
            if '\n' in s2:
                s2 = f'({indent(s2, 2, first_line=1)})'
            else:
                s2 = f'({s2})'
        if self.op in ('=', '+', '-', '*', '/', '<=', '>=', '>', '<', '%', '!=', '&', '|'):
            return f'{s1} {self.op} {s2}'
        elif self.op in '->':
            if isinstance(self.expr2, OpExpr) and self.expr2.op == '->':
                return f'({s1}) -> ({indent(s2, 2)})'
            else:
                return f'({s1}) -> {indent(s2, 2)}'
        else:
            raise NotImplementedError

    def __repr__(self):
        return f'OpExpr({self.op}, {self.expr1}, {self.expr2})'

    def __eq__(self, other):
        return isinstance(other, OpExpr) and self.op == other.op and self.expr1 == other.expr1 and self.expr2 == other.expr2

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], is_prime=True) -> BaseExpr:
        self.expr1 = self.expr1.elaborate(prot, bound_vars, is_prime)
        self.expr2 = self.expr2.elaborate(prot, bound_vars, is_prime)
        # todo: "Crit"
        #       n[i] = T& x = true
        expr1_list = [self.expr1.z3_expr] if not isinstance(self.expr1, ArrayIndex) else self.expr1.z3_expr
        expr2_list = [self.expr2.z3_expr] if not isinstance(self.expr2, ArrayIndex) else self.expr2.z3_expr
        if isinstance(self.expr1, ArrayIndex) ^ isinstance(self.expr2, ArrayIndex):
            self.z3_expr = [operator_map[self.op](expr1, expr2) for expr1 in expr1_list for expr2 in expr2_list]
        else:
            assert len(expr1_list) == len(expr2_list)
            self.z3_expr = [operator_map[self.op](expr1, expr2) for expr1, expr2 in zip(expr1_list, expr2_list)]
            if len(self.z3_expr) == 1:
                self.z3_expr = self.z3_expr[0]
        return self


class IntExpr(BaseExpr):
    def __init__(self, expr):
        super().__init__(expr)
        self.expr: int = expr

    def priority(self):
        return 80

    def __str__(self):
        s = str(self.expr)
        return s

    def __eq__(self, other):
        return isinstance(other, IntExpr) and self.expr == other.expr

    def __repr__(self):
        return f'INT({self.expr})'

    def elaborate(self, prot, bound_vars, is_prime=True):
        return self


class NegExpr(BaseExpr):
    def __init__(self, expr: BaseExpr):
        super().__init__()
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

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], is_prime=True) -> BaseExpr:
        self.expr = self.expr.elaborate(prot, bound_vars, is_prime)
        self.z3_expr = Not(self.expr.z3_expr)
        return self


class BaseCmd:
    def __init__(self, z3_expr=None):
        self.z3_expr: DatatypeRef = z3_expr

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], is_prime=True) -> "BaseCmd":
        return self


class UndefineCmd(BaseCmd):
    def __init__(self, var):
        super().__init__()
        self.var = var

    def __str__(self):
        return f'undefine {self.var};'

    def __repr__(self):
        return f'UndefineCmd({self.var})'

    def __eq__(self, other):
        return isinstance(other, UndefineCmd) and self.var == other.var

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], is_prime=True) -> "BaseCmd":
        self.var = self.var.elaborate(prot, bound_vars, is_prime)
        return self


class AssignCmd(BaseCmd):
    def __init__(self, var, expr):
        super().__init__()
        assert isinstance(var, BaseExpr)
        self.var = var
        self.expr = expr

    def __str__(self):
        return indent(f'{self.var} := {self.expr};\n', 0)

    def __repr__(self):
        return f'AssignCmd({self.var}, {self.expr})'

    def __eq__(self, other):
        return isinstance(other, AssignCmd) and self.var == other.var and self.expr == other.expr

    def elaborate(self, prot, bound_vars, is_prime=True):
        self.var = self.var.elaborate(prot, bound_vars, is_prime)
        self.expr = self.expr.elaborate(prot, bound_vars, is_prime)
        if isinstance(self.var, ArrayIndex):
            assert isinstance(self.var.z3_expr, list)
            self.z3_expr = [var == self.expr.z3_expr for var in self.var.z3_expr]
        else:
            self.z3_expr = self.var.z3_expr == self.expr.z3_expr
        return self


class ForallCmd(BaseCmd):
    def __init__(self, var_decl, cmds):
        super().__init__()
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

    def elaborate(self, prot, bound_vars, is_prime=True):
        self.cmds = [cmd.elaborate(prot, bound_vars | {self.var: self.typ}, is_prime) for cmd in self.cmds]
        self.z3_expr = And([cmd.z3_expr for cmd in self.cmds])
        return self


class IfCmd(BaseCmd):
    def __init__(self, args):
        super().__init__()
        assert len(args) > 1
        self.args = args
        self.if_branches = None
        self.else_branch = None

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

    def elaborate(self, prot, bound_vars, is_prime=True):
        args = [arg.elaborate(prot, bound_vars, is_prime) for arg in self.args]
        self.if_branches = list(zip(args[::2], args[1::2]))
        self.else_branch = args[-1] if len(args) % 2 == 1 else None
        return self


class ProtDecl:
    def __init__(self, is_startstate, z3_expr=None):
        self.z3_expr: Optional[DatatypeRef] = z3_expr
        self.is_startstate: bool = is_startstate

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
        self.cmds: list[BaseCmd] = [cmd.elaborate(prot, bound_vars, is_prime=False) for cmd in self.cmds]
        return self


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
        return isinstance(other,
                          MurphiRule) and self.name == other.name and self.cond == other.cond and self.cmds == other.cmds

    def elaborate(self, prot, bound_vars):
        self.cond = self.cond.elaborate(prot, bound_vars)
        self.cmds = [cmd.elaborate(prot, bound_vars) for cmd in self.cmds]
        return self


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
        self.inv = self.inv.elaborate(prot, bound_vars)
        return self


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
        self.rules = [rule.elaborate(prot, bound_vars | self.var_map) for rule in self.rules]
        return self


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
            typ_decl.elaborate(self)
            self.typ_map[typ_decl.name] = typ_decl.typ
            if isinstance(typ_decl.typ, EnumType):
                self.enum_typ_map[typ_decl.name] = typ_decl.typ
                for enum_val in typ_decl.typ.names:
                    self.enum_map[enum_val] = typ_decl.typ

            if isinstance(typ_decl.typ, ScalarSetType):
                self.scalarset.append(typ_decl.name)

        # Process variables
        self.var_map = dict()
        self.var_z3_map = dict()
        self.var_map_prime = dict()
        self.var_z3_map_prime = dict()
        for var_decl in self.vars:
            self.var_map[var_decl.name] = var_decl.typ
            self.var_map_prime[f'{var_decl.name}\''] = var_decl.typ
        for var_decl in self.vars:
            var_decl.elaborate(self)
            self.var_z3_map[var_decl.name] = var_decl.z3_expr
            self.var_z3_map_prime[f'{var_decl.name}\''] = var_decl.z3_expr

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
