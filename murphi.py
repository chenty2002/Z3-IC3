import re
from typing import Optional, Callable

from z3 import *


inv_collector_name = '__inv'
ruleset_collector_name = '__ruleset'
prot_collector_name = '__prot'
for_cmd_collector_name = '__for_cmd'
for_cmd_used_var_collector_name = '__for_cmd_used_vars'
if_cmd_collector_name = '__if_cmd'
if_cmd_used_var_collector_name = '__if_cmd_used_vars'
for_expr_collector_name = '__for_expr'
prot_decl_collector_name = '__prot_decl'
rule_collector_name = '__rule'
rule_used_var_collector_name = '__rule_used_vars'


def indent(s, num_space, first_line=None, sep='\n'):
    """
    Indent the given string by adding spaces to each line.

    Parameters
    ----------
    s : str
    num_space : int
        Number of spaces to add to each line
    first_line : int, optional
        Number of spaces to add to first line
    sep : str, optional
    """
    lines = s.split('\n')
    if first_line is None:
        return sep.join(' ' * num_space + line for line in lines)
    else:
        res = ' ' * first_line + lines[0]
        if len(lines) > 1:
            res += sep + sep.join(' ' * num_space + line for line in lines[1:])
        return res


def indent_list(s: list[str], num_space, first_line=None, start: int = 0, sep='\n'):
    assert first_line is None or start > 0
    first_lines = sep.join(s[:start])
    return first_lines + sep + indent(sep.join(s[start:]), num_space)


def tuple_to_list(t):
    if isinstance(t, tuple):
        return [tuple_to_list(item) for item in t]
    return t


const_map = dict()
digitType_map = dict()
re_digitType_map = dict()
specific_typ = {}
specific_var = {}
specific_enum_var = {}


class UsedVar:
    def __init__(self, name: str, typ: "MurphiType", exec_typ: Optional[range | set] = None):
        self.name = name
        self.typ = typ
        self.exec_typ = exec_typ


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
    def __init__(self, z3_type=None, exec_str=''):
        self.z3_type: Optional[DatatypeSortRef | range | int | bool] = z3_type
        self.exec_str: str = exec_str

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
            self.exec_str = prot.var_map[self.name].exec_str
        elif self.name in prot.typ_map:
            self.z3_type = prot.typ_map[self.name].z3_type
            self.exec_str = prot.typ_map[self.name].exec_str
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
        self.exec_str = 'IntSort()'
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
        self.z3_type = range(down-1, up)
        self.exec_str = f'range({down-1}, {up})'


class BooleanType(MurphiType):
    __instance = None

    def __new__(cls, *args, **kwargs):
        if cls.__instance is None:
            cls.__instance = super().__new__(cls)
        return cls.__instance

    def __init__(self):
        super().__init__(BoolSort(), 'BoolSort()')

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
        typ_name = kwargs['typ_name']
        self.z3_type, enum_val = EnumSort(typ_name, self.names)
        names = ', '.join(self.names)
        names_str = ', '.join(f'\'{name}\'' for name in self.names)
        self.exec_str = f'{typ_name}, ({names}) = EnumSort(\'{typ_name}_test\', [{names_str}])'
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
        self.ele_z3_type = None
        self.idx_z3_type = None
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
        self.exec_str = self.ele_typ.exec_str


class RecordType(MurphiType):
    __instances = dict()

    def __new__(cls, *args, **kwargs):
        idx = tuple(map(lambda arg: arg.name, *args))
        if idx not in cls.__instances:
            cls.__instances[idx] = super().__new__(cls)
        return cls.__instances[idx]

    def __init__(self, typ_decls):
        super().__init__()
        self.typ_name = ''
        self.typ_decls = typ_decls
        self.attrs = {}

    def __str__(self):
        decls = '\n'.join(indent(str(decl), 2) + ';' for decl in self.typ_decls)
        return f'record\n{decls}\nend'

    def __repr__(self):
        decls = ', '.join(repr(decl) for decl in self.typ_decls)
        return f'RecordType({decls})'

    def __eq__(self, other):
        return isinstance(other, RecordType) and self.typ_decls == other.typ_decls

    def __hash__(self):
        return hash(tuple(map(lambda arg: arg.name, self.typ_decls)))

    def elaborate(self, prot: "MurphiProtocol", **kwargs):
        for typ_decl in self.typ_decls:
            typ_decl.elaborate(prot)
            self.attrs[typ_decl.name] = typ_decl.typ
        self.typ_name = kwargs['typ_name']
        exec_str = [f'{self.typ_name} = Datatype(\'{self.typ_name}\')']
        attr_list = []
        for attr in self.typ_decls:
            assert isinstance(attr.typ, VarType)
            if attr.typ.exec_str.startswith('range'):
                attr_list.append(f'(\'{attr.name}\', IntSort())')
            else:
                attr_list.append(f'(\'{attr.name}\', {attr.typ.name})')
        attr_str = ', '.join(attr_list)
        exec_str.append(f'{self.typ_name}.declare(\'mk_{self.typ_name}\', {attr_str})')
        exec_str.append(f'{self.typ_name} = {self.typ_name}.create()')
        self.exec_str = '\n'.join(exec_str)
        self.z3_type = Datatype(self.typ_name)


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
        # self.z3_expr: Optional[DatatypeRef] = None
        self.exec_str: str = ''
        self.prime_exec_str: str = ''

    def __str__(self):
        return f'{self.name} : {self.typ}'

    def __repr__(self):
        return f'MurphiVarDecl({repr(self.name)}, {self.typ})'

    def __eq__(self, other):
        return isinstance(other, MurphiVarDecl) and self.name == other.name and self.typ == other.typ

    def elaborate(self, prot: "MurphiProtocol"):
        self.typ.elaborate(prot, typ_name=self.name)
        if isinstance(self.typ, EnumType) or isinstance(self.typ, RecordType):
            typ_exec_str = self.name
            self.exec_str = self.typ.exec_str + '\n'
            self.prime_exec_str = self.typ.exec_str + '\n'
        elif isinstance(self.typ, VarType):
            if isinstance(prot.typ_map[self.typ.name], EnumType) or isinstance(prot.typ_map[self.typ.name], RecordType):
                typ_exec_str = self.typ.name
            elif isinstance(prot.typ_map[self.typ.name], RngType):
                typ_exec_str = 'IntSort()'
            else:
                typ_exec_str = self.typ.exec_str
        else:
            typ_exec_str = self.typ.exec_str
            self.exec_str = ''
            self.prime_exec_str = ''
        if isinstance(self.typ, ArrayType):
            assert isinstance(self.typ.idx_z3_type, range)
            # self.z3_expr = [Const(f'{self.name}[{i}]', self.typ.ele_z3_type) for i in self.typ.idx_z3_type]

            if isinstance(self.typ.ele_typ, VarType):
                if (isinstance(prot.typ_map[self.typ.ele_typ.name], EnumType) or
                        isinstance(prot.typ_map[self.typ.ele_typ.name], RecordType)):
                    typ_exec_str = self.typ.ele_typ.name
                elif isinstance(prot.typ_map[self.typ.ele_typ.name], RngType):
                    typ_exec_str = 'IntSort()'
            self.exec_str += (f'{self.name} = ['
                              f'Const(f\'{self.name}[{{i}}]\', {typ_exec_str}) '
                              f'for i in range({self.typ.idx_z3_type.start}, {self.typ.idx_z3_type.stop})'
                              f']')
            self.prime_exec_str += (f'{self.name}_ = ['
                                    f'Const(f\'{self.name}[{{i}}]\\\'\', {typ_exec_str}) '
                                    f'for i in range({self.typ.idx_z3_type.start}, {self.typ.idx_z3_type.stop})'
                                    f']')
        else:
            # self.z3_expr = Const(self.name, self.typ.z3_type)
            self.exec_str += f'{self.name} = Const(\'{self.name}\', {typ_exec_str})'
            self.prime_exec_str += f'{self.name}_ = Const(\'{self.name}\\\'\', {typ_exec_str})'


class BaseExpr:
    """Base class for Murphi expressions."""

    def __init__(self, z3_expr=None, exec_str=''):
        # self.z3_expr: Optional[DatatypeRef] = z3_expr
        self.exec_str: str | list[str] = exec_str
        self.loop_var: bool = False
        self.prime_pair: (str, str) = ('', '')
        # self.used_vars: dict[str, set[str]] = dict()

    def priority(self) -> int:
        raise NotImplementedError

    # for RecordType and FieldName
    def get_atom_type(self, prot: "MurphiProtocol", expr: "BaseExpr") -> str:
        if isinstance(expr, VarExpr):
            assert expr.name in prot.var_map
            if isinstance(expr.typ, ArrayType):
                if isinstance(expr.typ.ele_typ, VarType):
                    return expr.typ.ele_typ.name
            elif isinstance(expr.typ, RecordType):
                return expr.typ.typ_name
        elif isinstance(expr, FieldName):
            return self.get_atom_type(prot, expr.v)
        elif isinstance(expr, ArrayIndex):
            return self.get_atom_type(prot, expr.v)

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
        super().__init__(BoolVal(val), str(val))
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
        super().__init__(enum_type.enum_map[enum_val], enum_val)
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
        self.prime_pair = (self.name, f'{self.name}_')
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
            # self.z3_expr = bound_vars[self.name].z3_type
            self.exec_str = self.name
            self.loop_var = True
        else:
            if is_prime:
                # self.z3_expr = prot.var_z3_map_prime[self.name + '_']
                self.exec_str = self.name + '_'
                # self.used_vars[self.name] = set()
            else:
                # self.z3_expr = prot.var_z3_map[self.name]
                self.exec_str = self.name
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

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], is_prime=True) -> BaseExpr:
        self.v = self.v.elaborate(prot, bound_vars, is_prime)
        typ_name = self.get_atom_type(prot, self.v)
        self.exec_str = f'{typ_name}.{self.field}({self.v.exec_str})'
        self.prime_pair = (f'{typ_name}.{self.field}({self.v.prime_pair[0]})',
                           f'{typ_name}.{self.field}({self.v.prime_pair[1]})')
        # if is_prime:
        #     for var in self.v.used_vars.keys():
        #         if var not in self.used_vars:
        #             self.used_vars[var] = set()
        #         self.used_vars[var].update(f'{self.field}')
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
        self.exec_str = f'{self.v.exec_str}[{self.idx.exec_str}]'
        self.prime_pair = (f'{self.v.prime_pair[0]}[{self.idx.exec_str}]',
                           f'{self.v.prime_pair[1]}[{self.idx.exec_str}]')
        # if is_prime:
        #     for var in self.v.used_vars.keys():
        #         if var not in self.used_vars:
        #             self.used_vars[var] = set()
        #         self.used_vars[var].update(f'{self.idx.exec_str}')
        # if bound_vars:
        #     if isinstance(self.v, VarExpr) and isinstance(self.v.typ, ArrayType) and isinstance(self.idx.z3_expr, range):
        #         self.z3_expr = self.v.z3_expr
        #     else:
        #         raise ValueError('Array index error')
        return self


invVars = dict()


class ForallExpr(BaseExpr):
    cnt = 0

    def __init__(self, var_decl: MurphiVarDecl, expr: BaseExpr):
        super().__init__()
        ForallExpr.cnt += 1
        self.cnt = ForallExpr.cnt
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
        var_name = f'{self.var}_' if is_prime else self.var
        self.expr = self.expr.elaborate(prot, bound_vars | {var_name: self.typ}, is_prime)
        # if is_prime:
        #     for var, val in self.expr.used_vars.items():
        #         if var not in self.used_vars:
        #             self.used_vars[var] = set()
        #         self.used_vars[var] |= val
        self.exec_str = f'And(*[{self.expr.exec_str} for {self.var} in {self.typ.z3_type}])'
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
    '*': lambda a, b: a * b,
    '/': lambda a, b: a / b,
    '%': lambda a, b: a % b,
    '+': lambda a, b: a + b,
    '-': lambda a, b: a - b,
    '=': lambda a, b: a == b,
    '<=': lambda a, b: a <= b,
    '>=': lambda a, b: a >= b,
    '>': lambda a, b: a > b,
    '<': lambda a, b: a < b,
    '!=': lambda a, b: a != b,
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
        expr1_exec_str = self.expr1.exec_str
        expr2_exec_str = self.expr2.exec_str
        self.loop_var = self.expr1.loop_var and self.expr2.loop_var
        if self.op == '=':
            if isinstance(self.expr2, BooleanExpr):
                if self.expr2.val:
                    self.exec_str = expr1_exec_str
                else:
                    self.exec_str = f'Not({expr1_exec_str})'
            else:
                self.exec_str = f'{expr1_exec_str} == {expr2_exec_str}'
        elif self.op == '->':
            if self.expr1.loop_var:
                self.exec_str = [f'if {expr1_exec_str}:\n',
                                 f'{expr2_exec_str}']
            else:
                self.exec_str = f'Implies({expr1_exec_str}, {expr2_exec_str})'
        elif self.op == '&':
            self.exec_str = f'And({expr1_exec_str}, {expr2_exec_str})'
        elif self.op == '|':
            self.exec_str = f'Or({expr1_exec_str}, {expr2_exec_str})'
        else:
            self.exec_str = f'{expr1_exec_str} {self.op} {expr2_exec_str}'
        return self


class IntExpr(BaseExpr):
    def __init__(self, expr):
        super().__init__(expr, str(expr))
        self.expr: int = expr
        self.loop_var = True

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
        # self.z3_expr = Not(self.expr.z3_expr)
        self.exec_str = f'Not({self.expr.exec_str})'
        # if is_prime:
        #     for var, val in self.expr.used_vars.items():
        #         if var not in self.used_vars:
        #             self.used_vars[var] = set()
        #         self.used_vars[var] |= val
        return self


class BaseCmd:
    def __init__(self, z3_expr=None, exec_str=''):
        # self.z3_expr: DatatypeRef = z3_expr

        # string composing the expressions for exec in python
        # ForallCmd: self.exec_str = commands, {for_cmd_collector_name}_{self.cnt} = result
        # IfCmd: self.exec_str = commands, {if_cmd_collector_name}_{self.cnt} = result
        # Others: self.exec_str = command expression
        self.exec_str: str = exec_str

        # used variables in one command (var, var_prime)
        # ForallCmd: {for_cmd_used_var_collector_name}_{self.cnt}, _
        # IfCmd: {if_cmd_used_var_collector_name}_{self.cnt}. _
        # Others: {var, var_prime}
        self.used_vars_collector: list[(str, str)] = []

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
        self.expr = self.expr.elaborate(prot, bound_vars, False)
        # if isinstance(self.var, ArrayIndex):
        #     assert isinstance(self.var.z3_expr, list)
        #     self.z3_expr = [var == self.expr.z3_expr for var in self.var.z3_expr]
        # else:
        #     self.z3_expr = self.var.z3_expr == self.expr.z3_expr

        # prime_str = '_' if is_prime and not isinstance(self.var, ArrayIndex) else ''
        prime_pair = self.var.prime_pair
        var_exec_str = prime_pair[1] if is_prime else prime_pair[0]

        if isinstance(self.expr, BooleanExpr):
            # var == True/False
            if self.expr.val:
                self.exec_str = f'{var_exec_str}'
            else:
                self.exec_str = f'Not({var_exec_str})'
        else:
            self.exec_str = f'{var_exec_str} == {self.expr.exec_str}'
        if is_prime:
            self.used_vars_collector.append((f'{prime_pair[0]}', f'{prime_pair[1]}'))
        # if is_prime:
        #     for var, val in self.var.used_vars.items():
        #         if var not in self.used_vars[0]:
        #             self.used_vars[0][var] = set()
        #         self.used_vars[0][var] |= val
        return self


class ForallCmd(BaseCmd):
    cnt = 0

    def __init__(self, var_decl, cmds):
        super().__init__()
        ForallCmd.cnt += 1
        self.cnt = ForallCmd.cnt
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
        # cmd_expr = [expr for cmd in self.cmds for expr in (cmd.z3_expr if isinstance(cmd.z3_expr, list) else [cmd.z3_expr])]
        # self.z3_expr = And(cmd_expr)
        # if is_prime:
        #     for cmd in self.cmds:
        #         for var, val in cmd.used_vars.items():
        #             if var not in self.used_vars:
        #                 self.used_vars[var] = set()
        #             self.used_vars[var] |= val
        exec_str = []
        indent_start = 2
        if is_prime:
            self.used_vars_collector.append((f'{for_cmd_used_var_collector_name}_{self.cnt}', ''))
            exec_str.append(f'{for_cmd_used_var_collector_name}_{self.cnt} = set()')
            indent_start = 3
        exec_str += [f'{for_cmd_collector_name}_{self.cnt} = []',
                     f'for {self.var} in {self.typ.z3_type}:']
        for cmd in self.cmds:
            if isinstance(cmd, ForallCmd):
                exec_str.append(f'{for_cmd_collector_name}_{self.cnt} += {for_cmd_collector_name}_{cmd.cnt})')
                if is_prime:
                    exec_str.append(f'{for_cmd_used_var_collector_name}_{self.cnt} |= {for_cmd_used_var_collector_name}_{cmd.cnt}')
            elif isinstance(cmd, IfCmd):
                exec_str.append(f'{for_cmd_collector_name}_{self.cnt} += {if_cmd_collector_name}_{cmd.cnt})')
                if is_prime:
                    exec_str.append(f'{for_cmd_used_var_collector_name}_{self.cnt} |= {if_cmd_used_var_collector_name}_{cmd.cnt}')
            else:
                exec_str.append(f'{for_cmd_collector_name}_{self.cnt}.append({cmd.exec_str})')
                if is_prime:
                    for used_var, used_prime in cmd.used_vars_collector:
                        exec_str.append(f'{for_cmd_used_var_collector_name}_{self.cnt}.add('
                                        f'({used_var}, {used_prime}))')
        self.exec_str = indent_list(exec_str, 4, 0, indent_start,  '\n')
        return self


class IfCmd(BaseCmd):
    cnt = 0

    def __init__(self, args):
        super().__init__()
        assert len(args) > 1
        IfCmd.cnt += 1
        self.cnt = IfCmd.cnt
        self.args = args
        self.if_branches = tuple_to_list(tuple(zip(args[::2], args[1::2])))
        self.else_branch = args[-1] if len(args) % 2 == 1 else None
        # self.if_exec_str = []
        # self.else_exec_str = ''

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

    def get_branch_exec_str(self,
                            branch: list[BaseCmd],
                            branch_collector_name,
                            branch_used_var_collector_name,
                            is_prime=True):
        branch_exec_str = [f'{branch_collector_name} = []', f'{branch_used_var_collector_name} = set()']
        for cmd in branch:
            if isinstance(cmd, ForallCmd):
                branch_exec_str.append(f'{branch_collector_name} += {for_cmd_collector_name}_{cmd.cnt}')
                if is_prime:
                    branch_exec_str.append(f'{branch_used_var_collector_name} |= {for_cmd_used_var_collector_name}_{cmd.cnt}')
            elif isinstance(cmd, IfCmd):
                branch_exec_str.append(f'{branch_collector_name} += {if_cmd_collector_name}_{cmd.cnt}')
                if is_prime:
                    branch_exec_str.append(f'{branch_used_var_collector_name} |= {if_cmd_used_var_collector_name}_{cmd.cnt}')
            else:
                branch_exec_str.append(f'{branch_collector_name}.append({cmd.exec_str})')
                if is_prime:
                    for used_var, used_prime in cmd.used_vars_collector:
                        branch_exec_str.append(f'{branch_used_var_collector_name}.add('
                                               f'({used_var}, {used_prime}))')
        return branch_exec_str

    def elaborate(self, prot, bound_vars, is_prime=True):
        if is_prime:
            self.used_vars_collector.append((f'{if_cmd_used_var_collector_name}_{self.cnt}', ''))
        exec_str = [f'{if_cmd_collector_name}_{self.cnt} = []',
                    f'{if_cmd_used_var_collector_name}_{self.cnt} = set()']

        branch_collector_name = '__if_branch'
        branch_used_var_collector_name = '__if_branch_used_vars'
        last_branch_condition = 'True'
        for branch in self.if_branches:
            branch[0] = branch[0].elaborate(prot, bound_vars, False)
            branch[1] = [cmd.elaborate(prot, bound_vars, is_prime) for cmd in branch[1]]

            exec_str += self.get_branch_exec_str(branch[1], branch_collector_name, branch_used_var_collector_name, is_prime)

            if last_branch_condition == 'True':
                if_exec_str = f'And({branch[0].exec_str}, *{branch_collector_name})'
            else:
                if_exec_str = f'And({last_branch_condition}, {branch[0].exec_str}, *{branch_collector_name})'
            last_branch_condition = f'And({last_branch_condition}, Not({branch[0].exec_str}))'

            exec_str.append(f'{if_cmd_collector_name}_{self.cnt}.append({if_exec_str})')

        if self.else_branch:
            self.else_branch = [cmd.elaborate(prot, bound_vars, is_prime) for cmd in self.else_branch]

            exec_str += self.get_branch_exec_str(self.else_branch, branch_collector_name, branch_used_var_collector_name, is_prime)

            exec_str.append(f'{if_cmd_collector_name}_{self.cnt}.append(And({last_branch_condition}, *{branch_collector_name}))')

        self.exec_str = '\n'.join(exec_str)
        return self


class ProtDecl:
    def __init__(self, is_startstate, is_invariant, z3_expr=None, exec_str=''):
        # self.z3_expr: Optional[DatatypeRef] = z3_expr
        self.is_startstate: bool = is_startstate
        self.is_invariant: bool = is_invariant
        self.exec_str: str = exec_str

    def elaborate(self, prot, bound_vars):
        pass


class StartState(ProtDecl):
    def __init__(self, args):
        super().__init__(True, False)
        assert len(args) < 3
        if len(args) == 1:
            self.name = '__init__'
            self.cmds = args[0]
        else:
            self.name, self.cmds = args
            self.name = self.name.replace('"', '')

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
        # self.z3_expr = And([cmd.z3_expr for cmd in self.cmds])
        exec_str = [f'{prot_decl_collector_name}_{self.name} = []']
        for cmd in self.cmds:
            if isinstance(cmd, ForallCmd):
                exec_str.append(cmd.exec_str)
                exec_str.append(f'{prot_decl_collector_name}_{self.name}.extend({for_cmd_collector_name}_{cmd.cnt})')
            else:
                exec_str.append(f'{prot_decl_collector_name}_{self.name}.append({cmd.exec_str})')
        self.exec_str = '\n'.join(exec_str)
        return self


class MurphiRule(ProtDecl):
    def __init__(self, args):
        super().__init__(False, False)
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
        # self.used_vars: dict[str, set[str]] = dict()

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
        self.cond = self.cond.elaborate(prot, bound_vars, is_prime=False)
        self.cmds = [cmd.elaborate(prot, bound_vars) for cmd in self.cmds]
        # expr_width = max(*[len(cmd.z3_expr) for cmd in self.cmds if isinstance(cmd.z3_expr, list)], 1)
        # cond_expr_list = [self.cond.z3_expr] * expr_width if not isinstance(self.cond.z3_expr, list) else self.cond.z3_expr
        # assert len(cond_expr_list) == expr_width
        # cmd_expr_list = []
        # for i in range(expr_width):
        #     cmd_expr_list.append(And(cond_expr_list[i],
        #                              *[cmd.z3_expr[i] if isinstance(cmd.z3_expr, list) else cmd.z3_expr for cmd in self.cmds]))
        # self.z3_expr = Or(cmd_expr_list)
        exec_str = [f'{rule_collector_name}_{self.name} = []',
                    f'{rule_used_var_collector_name}_{self.name} = {set()}']
        for cmd in self.cmds:
            if isinstance(cmd, ForallCmd):
                exec_str.append(cmd.exec_str)
                exec_str.append(f'{rule_collector_name}_{self.name}.extend({for_cmd_collector_name}_{cmd.cnt})')
            elif isinstance(cmd, IfCmd):
                exec_str.append(cmd.exec_str)
                exec_str.append(f'{rule_collector_name}_{self.name}.extend({if_cmd_collector_name}_{cmd.cnt})')
            else:
                exec_str.append(f'{rule_collector_name}_{self.name}.append({cmd.exec_str})')

        for cmd in self.cmds:
            if isinstance(cmd, ForallCmd):
                exec_str.append(f'{rule_used_var_collector_name}_{self.name} |= {for_cmd_used_var_collector_name}_{cmd.cnt}')
            elif isinstance(cmd, IfCmd):
                exec_str.append(f'{rule_used_var_collector_name}_{self.name} |= {if_cmd_used_var_collector_name}_{cmd.cnt}')
            else:
                for used_var, used_prime in cmd.used_vars_collector:
                    exec_str.append(f'{rule_used_var_collector_name}_{self.name}.add(('
                                    f'{used_var}, {used_prime}))')

        exec_str.append(f'__unused_vars_{self.name} = set(zip(variables, primes)) - {rule_used_var_collector_name}_{self.name}')
        exec_str.append(f'for (var, var_) in __unused_vars_{self.name}:')
        exec_str.append(f'    {rule_collector_name}_{self.name}.append(var_ == var)')
        exec_str.append(f'{prot_decl_collector_name}_{self.name}.append('
                        f'And({self.cond.exec_str}, *{rule_collector_name}_{self.name})'
                        f')')
        self.exec_str = '\n'.join(exec_str)
        return self


class MurphiInvariant(ProtDecl):
    def __init__(self, name, inv):
        super().__init__(False, True)
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
        self.inv = self.inv.elaborate(prot, bound_vars, is_prime=False)
        # self.z3_expr = self.inv.z3_expr
        if isinstance(self.inv.exec_str, list) and len(self.inv.exec_str) == 2:
            self.exec_str = (f'{self.inv.exec_str[0]}'
                             f'    {prot_decl_collector_name}_{self.name}.append({self.inv.exec_str[1]})')
        else:
            self.exec_str = f'{prot_decl_collector_name}_{self.name}.append({self.inv.exec_str})'
        return self


class MurphiRuleSet(ProtDecl):
    cnt = 0

    def __init__(self, var_decls: list[MurphiVarDecl], rules: list[MurphiRule | MurphiInvariant | StartState]):
        super().__init__(True in [isinstance(rule, StartState) for rule in rules],
                         True in [isinstance(rule, MurphiInvariant) for rule in rules])
        MurphiRuleSet.cnt += 1
        self.cnt = MurphiRuleSet.cnt
        if self.is_invariant:
            assert all(isinstance(rule, MurphiInvariant) for rule in rules)
        self.var_decls = var_decls
        self.var_map = dict()
        for var_decl in self.var_decls:
            self.var_map[var_decl.name] = var_decl.typ
        self.rules = rules
        if self.is_startstate:
            assert len(self.rules) == 1

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
        # if not self.is_invariant:
        #     self.z3_expr = Or([rule.z3_expr for rule in self.rules]) if not self.is_startstate else self.rules[0].z3_expr
        # else:
        #     self.z3_expr = And([rule.z3_expr for rule in self.rules])

        exec_str = [f'# ruleset {self.cnt}',
                    f'{ruleset_collector_name}_{self.cnt} = []']
        for_loop_str = []
        loop_cnt = 0
        for rule in self.rules:
            exec_str.append(f'{prot_decl_collector_name}_{rule.name} = []')
        for decl in self.var_decls:
            for_loop_str.append(indent(f'for {decl.name} in {decl.typ.z3_type}:', 4*loop_cnt))
            loop_cnt += 1
        for rule in self.rules:
            exec_str.append(f'\n# rule {rule.name} of ruleset {self.cnt}')
            exec_str.extend(for_loop_str)
            exec_str.append(indent(rule.exec_str, 4*loop_cnt))
            if rule.is_invariant or rule.is_startstate:
                exec_str.append(indent(f'{ruleset_collector_name}_{self.cnt}.append(And(*{prot_decl_collector_name}_{rule.name}))', 4*loop_cnt))
            else:
                exec_str.append(indent(f'{ruleset_collector_name}_{self.cnt}.append(Or(*{prot_decl_collector_name}_{rule.name}))', 0))
        self.exec_str = '\n'.join(exec_str)
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

        self.var_map = dict()
        # self.var_z3_map = dict()
        self.var_map_prime = dict()
        # self.var_z3_map_prime = dict()

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

        self.full_vars: set[(str, str)] = set()
        for var_decl in self.vars:
            self.var_map[var_decl.name] = var_decl.typ
            self.var_map_prime[f'{var_decl.name}_'] = var_decl.typ

        for var_decl in self.vars:
            var_decl.elaborate(self)
            if isinstance(var_decl.typ, ArrayType):
                assert isinstance(var_decl.typ.idx_z3_type, range)
                self.full_vars.add((f'{var_decl.name}[{i}]', f'{var_decl.name}_[{i}]') for i in var_decl.typ.idx_z3_type)
                # self.full_vars[var_decl.name] = UsedVar(var_decl.name, var_decl.typ, var_decl.typ.idx_z3_type)
            elif isinstance(var_decl.typ, RecordType):
                self.full_vars.add((f'{var_decl.name}.{attr}', f'{var_decl.name}_.{attr}') for attr in var_decl.typ.attrs.keys())
                # self.full_vars[var_decl.name] = UsedVar(var_decl.name, var_decl.typ, set(var_decl.typ.attrs.keys()))
            else:
                self.full_vars.add((var_decl.name, f'{var_decl.name}_'))
                # self.full_vars[var_decl.name] = UsedVar(var_decl.name, var_decl.typ, set())
            # self.var_z3_map[var_decl.name] = var_decl.z3_expr
            # self.var_z3_map_prime[f'{var_decl.name}_'] = var_decl.z3_expr

        # Elaboration
        for decl in self.decls:
            decl.elaborate(self, dict())
        start_states = list(filter(lambda decl: decl.is_startstate, self.decls))
        assert len(start_states) == 1
        self.start_state = start_states[0]

        if isinstance(self.start_state, StartState):
            self.init_exec_str = '\n'.join([self.start_state.exec_str,
                                            f'init = simplify(And(*{prot_decl_collector_name}_{self.start_state.name}))'])
        elif isinstance(self.start_state, MurphiRuleSet):
            self.init_exec_str = '\n'.join([self.start_state.exec_str,
                                            f'init = simplify(Or(*{ruleset_collector_name}_{self.start_state.cnt}))'])

        prot_exec_str = [f'{prot_collector_name} = []']
        inv_exec_str = [f'{inv_collector_name} = []']
        for decl in self.decls:
            if decl.is_startstate:
                continue
            if decl.is_invariant:
                if isinstance(decl, MurphiInvariant):
                    inv_exec_str.append(f'{prot_decl_collector_name}_{decl.name} = []')
                inv_exec_str.append(decl.exec_str)
                if isinstance(decl, MurphiInvariant):
                    inv_exec_str.append(f'{inv_collector_name}.append(And(*{prot_decl_collector_name}_{decl.name}))')
                elif isinstance(decl, MurphiRuleSet):
                    inv_exec_str.append(f'{inv_collector_name}.append(And(*{ruleset_collector_name}_{decl.cnt}))')
                else:
                    raise NotImplementedError
                inv_exec_str.append('\n')
            else:
                if isinstance(decl, MurphiRule):
                    prot_exec_str.append(f'{prot_decl_collector_name}_{decl.name} = []')
                prot_exec_str.append(decl.exec_str)
                prot_exec_str.append('\n')

        self.prot_exec_str = '\n'.join(prot_exec_str)
        self.inv_exec_str = '\n'.join(inv_exec_str)

        self.var_decl_exec_str = '\n'.join(var_decl.exec_str for var_decl in self.vars)
        self.prime_var_decl_exec_str = '\n'.join(var_decl.prime_exec_str for var_decl in self.vars)

        self.typ_decl_exec_str = '\n'.join(typ_decl.typ.exec_str for typ_decl in self.types
                                           if isinstance(typ_decl.typ, EnumType) or
                                           isinstance(typ_decl.typ, RecordType))
        # self.z3_expr = Or([decl.z3_expr for decl in self.decls if not decl.is_startstate])

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
        return (f'MurphiProtocol('
                f'{repr(self.consts)}, '
                f'{repr(self.types)}, '
                f'{repr(self.vars)}, '
                f'{repr(self.start_state)}, '
                f'{repr(self.decls)}'
                f')')

    def to_z3(self):
        var_collector = ''
        for var_name, typ in self.var_map.items():
            if isinstance(typ, ArrayType):
                var_collector += f'variables.extend({var_name})\n'
            else:
                var_collector += f'variables.append({var_name})\n'
        var_prime_collector = ''
        for var_name, typ in self.var_map_prime.items():
            if isinstance(typ, ArrayType):
                var_prime_collector += f'primes.extend({var_name})\n'
            else:
                var_prime_collector += f'primes.append({var_name})\n'
        trans_collector = []
        for decl in self.decls:
            if decl.is_startstate or decl.is_invariant:
                continue
            if isinstance(decl, MurphiRule):
                trans_collector.append(f'*{prot_decl_collector_name}_{decl.name}')
            elif isinstance(decl, MurphiRuleSet):
                trans_collector.append(f'*{ruleset_collector_name}_{decl.cnt}')
            else:
                raise NotImplementedError
        trans_str = ', '.join(trans_collector)
        trans_exec = f'trans = simplify(Or({trans_str}))'
        inv_exec = f'post = simplify(And({inv_collector_name}))'
        global_vars = globals() | {'variables': [], 'primes': []}
        to_z3_exec_str = (f'# type declarations\n'
                          f'{self.typ_decl_exec_str}\n\n'
                          f'# variable declarations\n'
                          f'{self.var_decl_exec_str}\n\n'
                          f'# prime variable declarations\n'
                          f'{self.prime_var_decl_exec_str}\n\n'
                          f'# get z3 expression of variables\n'
                          f'{var_collector}\n'
                          f'# get z3 expression of primes\n'
                          f'{var_prime_collector}\n\n'
                          f'# rule declarations\n'
                          f'{self.prot_exec_str}\n'
                          f'# start state declarations\n'
                          f'{self.init_exec_str}\n\n'
                          f'# invariant declarations\n'
                          f'{self.inv_exec_str}\n'
                          f'# get z3 expression of transitions\n'
                          f'{trans_exec}\n\n'
                          f'# get z3 expression of invariants\n'
                          f'{inv_exec}\n'
                          )
        print(to_z3_exec_str)
        with open('exec_str.py', 'w') as f:
            f.write('from z3 import *\n\n\n')
            f.write('variables = []\n')
            f.write('primes = []\n\n')
            f.write(to_z3_exec_str)
            f.write('\n\nprint(variables, primes, init, trans, post)\n')
        exec(to_z3_exec_str, global_vars)
        variables = global_vars['variables']
        primes = global_vars['primes']
        init = global_vars['init']
        trans = global_vars['trans']
        post = global_vars['post']
        return variables, primes, init, trans, post
