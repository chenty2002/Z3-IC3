import copy
import re

from z3 import *
from utils import *

const_map = dict()
specific_var = {}


# for RecordType and FieldName
def get_atom_type(expr) -> str:
    if isinstance(expr, VarExpr) or isinstance(expr, VarType):
        if isinstance(expr.typ, ArrayType):
            if isinstance(expr.typ.ele_typ, VarType):
                return expr.typ.ele_typ.name
        elif isinstance(expr.typ, RecordType):
            return expr.typ.typ_name
        elif isinstance(expr.typ, RngType):
            return expr.exec_str
        elif isinstance(expr.typ, EnumType):
            return expr.name
    elif isinstance(expr, ArrayType):
        return get_atom_type(expr.ele_typ)
    elif isinstance(expr, FieldName):
        return get_atom_type(expr.v)
    elif isinstance(expr, ArrayIndex):
        return get_atom_type(expr.v)
    elif isinstance(expr, RecordType):
        return expr.typ_name
    return expr.exec_str


def expr2str(expr: "BaseExpr"):
    if not (isinstance(expr, OpExpr)):
        if isinstance(expr, NegExpr):
            neg_var_pt = re.sub(r'\[.*?]', '[_]', str(expr.expr))
            if (str(expr.expr) in specific_var.keys() and
                isinstance(specific_var[str(expr.expr)], BooleanType)) or \
                    (neg_var_pt in specific_var.keys() and isinstance(specific_var[neg_var_pt], BooleanType)):
                expr = OpExpr('=', expr.expr, BooleanExpr(False))
                return str(expr)
        else:
            var_pt = re.sub(r'\[.*?]', '[_]', str(expr))
            if (str(expr) in specific_var.keys() and
                isinstance(specific_var[str(expr)], BooleanType)) or \
                    (var_pt in specific_var.keys() and isinstance(specific_var[var_pt], BooleanType)):
                expr = OpExpr('=', expr, BooleanExpr(True))
                return str(expr)


def get_branch_exec_str(branch: list["BaseCmd"], is_prime=True):
    branch_exec_str = [f'{branch_collector_name} = []', f'{branch_used_var_collector_name} = set()']
    for cmd in branch:
        if isinstance(cmd, ForallCmd):
            branch_exec_str.append(f'{branch_collector_name} += {for_cmd_collector_name}_{cmd.cnt}')
            if is_prime:
                branch_exec_str.append(
                    f'{branch_used_var_collector_name} |= {for_cmd_used_var_collector_name}_{cmd.cnt}')
        elif isinstance(cmd, IfCmd):
            branch_exec_str.append(f'{branch_collector_name} += {if_cmd_collector_name}_{cmd.cnt}')
            if is_prime:
                branch_exec_str.append(
                    f'{branch_used_var_collector_name} |= {if_cmd_used_var_collector_name}_{cmd.cnt}')
        else:
            branch_exec_str.append(f'{branch_collector_name}.append({cmd.exec_str})')
            if is_prime:
                for used_var, used_prime in cmd.used_vars_collector:
                    branch_exec_str.append(f'{branch_used_var_collector_name}.add('
                                           f'({used_var}, {used_prime}))')
    return branch_exec_str


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
    def __init__(self, exec_str=''):
        self.exec_str: str = exec_str

    def elaborate(self, prot: "MurphiProtocol", **kwargs):
        raise NotImplementedError


class VarType(MurphiType):
    def __init__(self, name):
        super().__init__()
        self.name = name
        self.typ = None

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
            self.exec_str = prot.var_map[self.name].exec_str
            self.typ = prot.var_map[self.name]
        elif self.name in prot.typ_map:
            self.exec_str = prot.typ_map[self.name].exec_str
            self.typ = prot.typ_map[self.name]
        else:
            raise ValueError(f'Variable {self.name} not declared')


class RngType(MurphiType):
    def __init__(self, down_rng: str, up_rng: str):
        super().__init__()
        self.exec_str = 'IntSort()'
        self.downRng = down_rng
        self.upRng = up_rng
        self.down_val = None
        self.up_val = None

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
        self.down_val = down
        self.up_val = up
        self.exec_str = f'range({up-down+1})'


class BooleanType(MurphiType):
    def __init__(self):
        super().__init__('BoolSort()')

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
    def __init__(self, names):
        super().__init__()
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

    def elaborate(self, prot: "MurphiProtocol", **kwargs):
        typ_name = kwargs['typ_name']
        names = ', '.join(self.names)
        names_str = ', '.join(f'\'{name}\'' for name in self.names)
        self.exec_str = f'{typ_name}, ({names}) = EnumSort(\'{typ_name}\', [{names_str}])'


class ArrayType(MurphiType):
    def __init__(self, idx_typ, ele_typ):
        super().__init__()
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
        self.exec_str = self.ele_typ.exec_str


class RecordType(MurphiType):
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
            attr_type = get_atom_type(attr.typ)
            if attr_type.startswith('range'):
                attr_list.append(f'(\'{attr.name}\', IntSort())')
            else:
                attr_list.append(f'(\'{attr.name}\', {attr_type})')
        attr_str = ', '.join(attr_list)
        exec_str.append(f'{self.typ_name}.declare(\'mk_{self.typ_name}\', {attr_str})')
        exec_str.append(f'{self.typ_name} = {self.typ_name}.create()')
        self.exec_str = '\n'.join(exec_str)


class MurphiTypeDecl:
    def __init__(self, name, typ):
        self.name = name
        self.typ: MurphiType = typ

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
        self.exec_str: str = ''
        self.prime_exec_str: str = ''

    def __str__(self):
        return f'{self.name} : {self.typ}'

    def __repr__(self):
        return f'MurphiVarDecl({repr(self.name)}, {self.typ})'

    def __eq__(self, other):
        return isinstance(other, MurphiVarDecl) and self.name == other.name and self.typ == other.typ

    def elaborate(self, prot: "MurphiProtocol", is_prime=False):
        if is_prime:
            self.name += '_'
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
            if isinstance(self.typ.ele_typ, VarType):
                if (isinstance(prot.typ_map[self.typ.ele_typ.name], EnumType) or
                        isinstance(prot.typ_map[self.typ.ele_typ.name], RecordType)):
                    typ_exec_str = self.typ.ele_typ.name
                elif isinstance(prot.typ_map[self.typ.ele_typ.name], RngType):
                    typ_exec_str = 'IntSort()'
            self.exec_str += (f'{self.name} = ['
                              f'Const(f\'{self.name}[{{i}}]\', {typ_exec_str}) '
                              f'for i in {self.typ.idx_typ.exec_str}'
                              f']')
            self.prime_exec_str += (f'{self.name}_ = ['
                                    f'Const(f\'{self.name}[{{i}}]\\\'\', {typ_exec_str}) '
                                    f'for i in {self.typ.idx_typ.exec_str}'
                                    f']')
        else:
            self.exec_str += f'{self.name} = Const(\'{self.name}\', {typ_exec_str})'
            self.prime_exec_str += f'{self.name}_ = Const(\'{self.name}\\\'\', {typ_exec_str})'


class BaseExpr:
    """Base class for Murphi expressions."""

    def __init__(self, exec_str=''):
        self.exec_str: str | list[str] = exec_str
        self.loop_var: bool = False
        self.prime_pair: (str, str) = (exec_str, exec_str)

    def priority(self) -> int:
        raise NotImplementedError

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], **kwargs) -> "BaseExpr":
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

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], **kwargs) -> BaseExpr:
        is_prime = kwargs.get('is_prime', True)
        obligation = kwargs.get('obligation', False)
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
        return expr.elaborate(prot, bound_vars, is_prime=is_prime, obligation=obligation)


class BooleanExpr(BaseExpr):
    def __init__(self, val):
        super().__init__(str(val))
        self.val = val

    def priority(self):
        return 100

    def __str__(self):
        return str(self.val)

    def __repr__(self):
        return f'BooleanExpr({repr(self.val)})'

    def __eq__(self, other):
        return isinstance(other, BooleanExpr) and self.val == other.val

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], **kwargs) -> BaseExpr:
        return self


class EnumValExpr(BaseExpr):
    def __init__(self, enum_type, enum_val):
        super().__init__(enum_val)
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

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], **kwargs) -> BaseExpr:
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

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], **kwargs) -> BaseExpr:
        is_prime = kwargs.get('is_prime', True)
        obligation = kwargs.get('obligation', False)
        if self.name in bound_vars:
            if obligation:
                self.name += '_'
            self.exec_str = self.name
            self.loop_var = True
        else:
            if is_prime:
                self.exec_str = self.name + '_'
            else:
                self.exec_str = self.name
        return self


class FieldName(BaseExpr):
    def __init__(self, var: BaseExpr, field: str):
        super().__init__()
        self.v = var
        self.field = field

    def priority(self):
        return 100

    def __str__(self):
        return f'{self.v}.{self.field}'

    def __repr__(self):
        return f'FieldName({repr(self.v)}, {repr(self.field)})'

    def __eq__(self, other):
        return isinstance(other, FieldName) and self.v == other.v and self.field == other.field

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], **kwargs) -> BaseExpr:
        is_prime = kwargs.get('is_prime', True)
        obligation = kwargs.get('obligation', False)
        self.v = self.v.elaborate(prot, bound_vars, is_prime=is_prime, obligation=obligation)
        typ_name = get_atom_type(self.v)
        self.exec_str = f'{typ_name}.{self.field}({self.v.exec_str})'
        self.prime_pair = (f'{typ_name}.{self.field}({self.v.prime_pair[0]})',
                           f'{typ_name}.{self.field}({self.v.prime_pair[1]})')
        return self


class ArrayIndex(BaseExpr):
    def __init__(self, var: BaseExpr, idx: BaseExpr):
        super().__init__()
        self.v = var
        self.idx = idx

    def priority(self):
        return 100

    def __str__(self):
        return f'{self.v}[{self.idx}]'

    def __repr__(self):
        return f'ArrayIndex({repr(self.v)}, {repr(self.idx)})'

    def __eq__(self, other):
        return isinstance(other, ArrayIndex) and self.v == other.v and self.idx == other.idx

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], **kwargs) -> BaseExpr:
        is_prime = kwargs.get('is_prime', True)
        obligation = kwargs.get('obligation', False)
        self.v = self.v.elaborate(prot, bound_vars, is_prime=is_prime, obligation=obligation)
        self.idx = self.idx.elaborate(prot, bound_vars, is_prime=False or obligation, obligation=obligation)
        self.exec_str = f'{self.v.exec_str}[{self.idx.exec_str}]'
        self.prime_pair = (f'{self.v.prime_pair[0]}[{self.idx.exec_str}]',
                           f'{self.v.prime_pair[1]}[{self.idx.exec_str}]')
        return self


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

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], **kwargs) -> BaseExpr:
        is_prime = kwargs.get('is_prime', True)
        obligation = kwargs.get('obligation', False)
        self.var_decl.elaborate(prot)

        self.expr = self.expr.elaborate(prot, bound_vars | {self.var: self.typ}, is_prime=is_prime, obligation=obligation)
        self.prime_pair = (f'And(*[{self.expr.exec_str} for {self.var} in {self.typ.exec_str}])',
                           f'And(*[{self.expr.prime_pair[1]} for {self.var}_ in {self.typ.exec_str}])')
        if is_prime:
            self.exec_str = self.prime_pair[1]
        else:
            self.exec_str = self.prime_pair[0]
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

    def get_exec_str(self, expr1, expr2, op):
        if op == '=':
            if isinstance(self.expr2, BooleanExpr):
                if self.expr2.val:
                    exec_str = expr1
                else:
                    exec_str = f'Not({expr1})'
            else:
                exec_str = f'{expr1} == {expr2}'
        elif op == '->':
            if self.expr1.loop_var:
                exec_str = [f'if {expr1}:\n', f'{expr2}']
            else:
                exec_str = f'Implies({expr1}, {expr2})'
        elif op == '&':
            exec_str = f'And({expr1}, {expr2})'
        elif op == '|':
            exec_str = f'Or({expr1}, {expr2})'
        else:
            exec_str = f'{expr1} {op} {expr2}'
        return exec_str

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], **kwargs) -> BaseExpr:
        is_prime = kwargs.get('is_prime', True)
        obligation = kwargs.get('obligation', False)
        self.expr1 = self.expr1.elaborate(prot, bound_vars, is_prime=is_prime, obligation=obligation)
        self.expr2 = self.expr2.elaborate(prot, bound_vars, is_prime=is_prime, obligation=obligation)
        assert isinstance(self.expr1.exec_str, str) and isinstance(self.expr2.exec_str, str)
        expr1_exec_str = self.expr1.exec_str
        expr1_prime_str = self.expr1.prime_pair[1]
        expr2_exec_str = self.expr2.exec_str
        expr2_prime_str = self.expr2.prime_pair[1]
        self.loop_var = self.expr1.loop_var and self.expr2.loop_var
        self.prime_pair = (self.get_exec_str(expr1_exec_str, expr2_exec_str, self.op),
                           self.get_exec_str(expr1_prime_str, expr2_prime_str, self.op))
        if is_prime:
            self.exec_str = self.prime_pair[1]
        else:
            self.exec_str = self.prime_pair[0]
        return self


class IntExpr(BaseExpr):
    def __init__(self, expr):
        super().__init__(str(expr))
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

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], **kwargs) -> BaseExpr:
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

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], **kwargs) -> BaseExpr:
        is_prime = kwargs.get('is_prime', True)
        obligation = kwargs.get('obligation', False)
        self.expr = self.expr.elaborate(prot, bound_vars, is_prime=is_prime, obligation=obligation)
        self.exec_str = f'Not({self.expr.exec_str})'
        return self


class BaseCmd:
    def __init__(self, exec_str=''):
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

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], **kwargs) -> "BaseCmd":
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

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], **kwargs) -> "BaseCmd":
        is_prime = kwargs.get('is_prime', True)
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

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], **kwargs) -> "BaseCmd":
        is_prime = kwargs.get('is_prime', True)
        self.var = self.var.elaborate(prot, bound_vars, is_prime=is_prime)
        self.expr = self.expr.elaborate(prot, bound_vars, is_prime=False)
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

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], **kwargs) -> "BaseCmd":
        is_prime = kwargs.get('is_prime', True)
        self.cmds = [cmd.elaborate(prot, bound_vars | {self.var: self.typ}, is_prime=is_prime) for cmd in self.cmds]
        self.var_decl.elaborate(prot)
        exec_str = []
        indent_start = 2
        if is_prime:
            self.used_vars_collector.append((f'{for_cmd_used_var_collector_name}_{self.cnt}', ''))
            exec_str.append(f'{for_cmd_used_var_collector_name}_{self.cnt} = set()')
            indent_start = 3
        exec_str += [f'{for_cmd_collector_name}_{self.cnt} = []',
                     f'for {self.var} in {self.typ.exec_str}:']
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

    def elaborate(self, prot: "MurphiProtocol", bound_vars: dict[str, MurphiType], **kwargs) -> "BaseCmd":
        is_prime = kwargs.get('is_prime', True)
        if is_prime:
            self.used_vars_collector.append((f'{if_cmd_used_var_collector_name}_{self.cnt}', ''))
        exec_str = [f'{if_cmd_collector_name}_{self.cnt} = []',
                    f'{if_cmd_used_var_collector_name}_{self.cnt} = set()']

        last_branch_condition = 'True'
        for branch in self.if_branches:
            branch[0] = branch[0].elaborate(prot, bound_vars, is_prime=False)
            branch[1] = [cmd.elaborate(prot, bound_vars, is_prime=is_prime) for cmd in branch[1]]

            exec_str += get_branch_exec_str(branch[1], is_prime)

            if_exec_str = f'And({last_branch_condition}, {branch[0].exec_str}, *{branch_collector_name})'
            last_branch_condition = f'And({last_branch_condition}, Not({branch[0].exec_str}))'

            exec_str.append(f'{if_cmd_collector_name}_{self.cnt}.append({if_exec_str})')

        if self.else_branch:
            self.else_branch = [cmd.elaborate(prot, bound_vars, is_prime=is_prime) for cmd in self.else_branch]

            exec_str += get_branch_exec_str(self.else_branch, is_prime)

            exec_str.append(f'{if_cmd_collector_name}_{self.cnt}.append(And({last_branch_condition}, *{branch_collector_name}))')

        self.exec_str = '\n'.join(exec_str)
        return self


class ProtDecl:
    def __init__(self, is_startstate, is_invariant, exec_str=''):
        self.is_startstate: bool = is_startstate
        self.is_invariant: bool = is_invariant
        self.exec_str: str = exec_str

    def elaborate(self, prot, bound_vars, obligation=False):
        return self


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

    def elaborate(self, prot, bound_vars, obligation=False):
        self.cmds: list[BaseCmd] = [cmd.elaborate(prot, bound_vars, is_prime=False) for cmd in self.cmds]
        exec_str = []
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

    def elaborate(self, prot, bound_vars, obligation=False):
        self.cond = self.cond.elaborate(prot, bound_vars, is_prime=False)
        self.cmds = [cmd.elaborate(prot, bound_vars) for cmd in self.cmds]
        exec_str = [f'{rule_cmds_collector_name}_{self.name} = []',
                    f'{rule_others_collector_name}_{self.name} = []',
                    f'{rule_used_var_collector_name}_{self.name} = set()']
        for cmd in self.cmds:
            if isinstance(cmd, ForallCmd):
                exec_str.append(cmd.exec_str)
                exec_str.append(f'{rule_cmds_collector_name}_{self.name}.extend({for_cmd_collector_name}_{cmd.cnt})')
            elif isinstance(cmd, IfCmd):
                exec_str.append(cmd.exec_str)
                exec_str.append(f'{rule_cmds_collector_name}_{self.name}.extend({if_cmd_collector_name}_{cmd.cnt})')
            else:
                exec_str.append(f'{rule_cmds_collector_name}_{self.name}.append({cmd.exec_str})')

        for cmd in self.cmds:
            if isinstance(cmd, ForallCmd):
                exec_str.append(f'{rule_used_var_collector_name}_{self.name} |= {for_cmd_used_var_collector_name}_{cmd.cnt}')
            elif isinstance(cmd, IfCmd):
                exec_str.append(f'{rule_used_var_collector_name}_{self.name} |= {if_cmd_used_var_collector_name}_{cmd.cnt}')
            else:
                for used_var, used_prime in cmd.used_vars_collector:
                    exec_str.append(f'{rule_used_var_collector_name}_{self.name}.add(('
                                    f'{used_var}, {used_prime}))')

        exec_str.append(f'__unused_vars_{self.name} = set(full_vars) - {rule_used_var_collector_name}_{self.name}')
        exec_str.append(f'for (var, var_) in __unused_vars_{self.name}:')
        exec_str.append(f'    {rule_others_collector_name}_{self.name}.append(var_ == var)')
        exec_str.append(f'{prot_decl_collector_name}_{self.name}.append('
                        f'(\'{self.name}\', {self.cond.exec_str}, And(*{rule_cmds_collector_name}_{self.name}), And(*{rule_others_collector_name}_{self.name}))'
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

    def elaborate(self, prot, bound_vars, obligation=False):
        self.inv = self.inv.elaborate(prot, bound_vars, is_prime=False or obligation, obligation=obligation)
        if obligation:
            collector = f'{prot_decl_collector_name}_{self.name}_prime'
        else:
            collector = f'{prot_decl_collector_name}_{self.name}'
        if isinstance(self.inv.exec_str, list) and len(self.inv.exec_str) == 2:
            self.exec_str = (f'{self.inv.exec_str[0]}'
                             f'    {collector}.append((\'{self.name}\', {self.inv.exec_str[1]}))')
        else:
            self.exec_str = f'{collector}.append((\'{self.name}\', {self.inv.exec_str}))'
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

    def elaborate(self, prot, bound_vars, obligation=False):
        self.rules = [rule.elaborate(prot, bound_vars | self.var_map, obligation) for rule in self.rules]
        exec_str = [f'# ruleset {self.cnt}']
        if self.is_startstate:
            exec_str.append(f'{ruleset_init_collector_name}_{self.cnt} = []')
        for_loop_str = []
        loop_cnt = 0
        for rule in self.rules:
            exec_str.append(f'{prot_decl_collector_name}_{rule.name} = []')
        for decl in self.var_decls:
            decl.elaborate(prot)
            for_loop_str.append(indent(f'for {decl.name} in {decl.typ.exec_str}:', 4*loop_cnt))
            loop_cnt += 1
        for rule in self.rules:
            exec_str.append(f'\n# rule {rule.name} of ruleset {self.cnt}')
            exec_str.extend(for_loop_str)
            exec_str.append(indent(rule.exec_str, 4*loop_cnt))
            if rule.is_startstate:
                exec_str.append(indent(f'{ruleset_init_collector_name}_{self.cnt}.append(And(*{prot_decl_collector_name}_{rule.name}))', 4*loop_cnt))
            elif rule.is_invariant:
                exec_str.append(indent(f'{atom_inv_collector_name}.extend({prot_decl_collector_name}_{rule.name})', 0))
            else:
                exec_str.append(indent(f'{atom_rule_collector_name}.extend({prot_decl_collector_name}_{rule.name})', 0))
        self.exec_str = '\n'.join(exec_str)
        return self


class MurphiProtocol:
    def __init__(self,
                 consts: list[MurphiConstDecl],
                 types: list[MurphiTypeDecl],
                 var_decls: list[MurphiVarDecl],
                 decls: list[ProtDecl]):
        self.consts = consts
        self.types = types
        self.vars = var_decls
        self.decls = decls

        self.typ_map = dict()
        self.enum_typ_map = dict()
        self.enum_map = dict()
        self.scalarset = list()

        self.var_map = dict()
        self.var_map_prime = dict()
        obligation = False

        # z3_var : range
        self.var_with_cons = {}

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
            var_decl_typ = var_decl.typ
            while isinstance(var_decl_typ, VarType):
                if var_decl_typ.name in self.typ_map:
                    var_decl_typ = self.typ_map[var_decl_typ.name]
                else:
                    var_decl_typ = self.var_map[var_decl_typ.name]
            if isinstance(var_decl_typ, ArrayType):
                self.full_vars |= self.traverse_array_types(var_decl.name, var_decl_typ)
            elif isinstance(var_decl_typ, RecordType):
                typ_name = get_atom_type(var_decl_typ)
                for (attr, typ) in var_decl_typ.attrs.items():
                    if isinstance(typ, VarType) and isinstance(typ.typ, RngType):
                        self.var_with_cons[f'{typ_name}.{attr}({var_decl.name})'] = typ.exec_str
                        self.var_with_cons[f'{typ_name}.{attr}({var_decl.name}_)'] = typ.exec_str
                    self.full_vars.add((f'{typ_name}.{attr}({var_decl.name})', f'{typ_name}.{attr}({var_decl.name}_)'))
            else:
                if isinstance(var_decl_typ, RngType):
                    self.var_with_cons[var_decl.name] = var_decl_typ.exec_str
                    self.var_with_cons[f'{var_decl.name}_'] = var_decl_typ.exec_str
                self.full_vars.add((var_decl.name, f'{var_decl.name}_'))

        full_vars_exec_str = ['full_vars = [']
        for (var, var_prime) in self.full_vars:
            full_vars_exec_str.append(f'    ({var}, {var_prime}),')
        full_vars_exec_str.append(']')
        self.full_vars_exec_str = '\n'.join(full_vars_exec_str)

        var_with_cons_exec_str = ['var_constraints = {']
        for var, cons in self.var_with_cons.items():
            assert cons.startswith('range')
            var_with_cons_exec_str.append(f'    {var}: {cons},')
        var_with_cons_exec_str.append('}')
        self.var_with_cons_exec_str = '\n'.join(var_with_cons_exec_str)

        # Elaboration
        for decl in self.decls:
            if decl.is_invariant or decl.is_startstate:
                decl.elaborate(self, dict())
        start_states = list(filter(lambda prot_decl: prot_decl.is_startstate, self.decls))
        assert len(start_states) == 1
        self.start_state = start_states[0]

        if isinstance(self.start_state, StartState):
            self.init_exec_str = '\n'.join([f'{prot_decl_collector_name}_{self.start_state.name} = []',
                                            self.start_state.exec_str,
                                            f'init = simplify(And(*{prot_decl_collector_name}_{self.start_state.name}))'])
        elif isinstance(self.start_state, MurphiRuleSet):
            self.init_exec_str = '\n'.join([self.start_state.exec_str,
                                            f'init = simplify(Or(*{ruleset_init_collector_name}_{self.start_state.cnt}))'])

        invariants = list(filter(lambda prot_decl: prot_decl.is_invariant, self.decls))
        self.invariants = invariants

        inv_exec_str = [f'{atom_inv_collector_name} = []']
        for inv in self.invariants:
            if isinstance(inv, MurphiInvariant):
                inv_exec_str.append(f'{prot_decl_collector_name}_{inv.name} = []')
            inv_exec_str.append(inv.exec_str)
            if isinstance(inv, MurphiInvariant):
                inv_exec_str.append(f'{atom_inv_collector_name}.extend({prot_decl_collector_name}_{inv.name})')
            inv_exec_str.append('\n')

        prot_exec_str = [f'{atom_rule_collector_name} = []']
        if obligation:
            prot_exec_str.append(f'{obligation_collector_name} = []')
        for decl in self.decls:
            if decl.is_startstate or decl.is_invariant:
                continue
            else:
                decl.elaborate(self, dict(), obligation)
                if isinstance(decl, MurphiRule):
                    prot_exec_str.append(f'# rule {decl.name}')
                    prot_exec_str.append(f'{prot_decl_collector_name}_{decl.name} = []')
                prot_exec_str.append(decl.exec_str)
                if isinstance(decl, MurphiRule):
                    prot_exec_str.append(f'{atom_rule_collector_name}.extend({prot_decl_collector_name}_{decl.name})')
                prot_exec_str.append('\n')

        self.prot_exec_str = '\n'.join(prot_exec_str)
        self.inv_exec_str = '\n'.join(inv_exec_str)

        self.var_decl_exec_str = '\n'.join(var_decl.exec_str for var_decl in self.vars)
        self.prime_var_decl_exec_str = '\n'.join(var_decl.prime_exec_str for var_decl in self.vars)

        self.typ_decl_exec_str = '\n'.join(typ_decl.typ.exec_str for typ_decl in self.types
                                           if isinstance(typ_decl.typ, EnumType) or
                                           isinstance(typ_decl.typ, RecordType))

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

    def traverse_array_types(self, name, typ: ArrayType) -> set[(str, str)]:
        exec_str = set()
        ele_typ = typ.ele_typ
        while isinstance(ele_typ, VarType):
            if ele_typ.name in self.typ_map:
                ele_typ = self.typ_map[ele_typ.name]
            else:
                ele_typ = self.var_map[ele_typ.name]
        if isinstance(ele_typ, ArrayType):
            typ_pairs = self.traverse_array_types(name, ele_typ)
            for i in eval(typ.idx_typ.exec_str):
                for (t, t_prime) in typ_pairs:
                    exec_str.add((f'{t}[{i}]', f'{t_prime}[{i}]'))
        elif isinstance(ele_typ, RecordType):
            typ_name = get_atom_type(typ)
            for i in eval(typ.idx_typ.exec_str):
                for (attr, typ) in ele_typ.attrs.items():
                    if isinstance(typ, VarType) and isinstance(typ.typ, RngType):
                        self.var_with_cons[f'{typ_name}.{attr}({name}[{i}])'] = typ.exec_str
                        self.var_with_cons[f'{typ_name}.{attr}({name}_[{i}])'] = typ.exec_str
                    exec_str.add((f'{typ_name}.{attr}({name}[{i}])', f'{typ_name}.{attr}({name}_[{i}])'))
        else:
            for i in eval(typ.idx_typ.exec_str):
                if isinstance(ele_typ, RngType):
                    self.var_with_cons[f'{name}[{i}]'] = ele_typ.exec_str
                    self.var_with_cons[f'{name}_[{i}]'] = ele_typ.exec_str
                exec_str.add((f'{name}[{i}]', f'{name}_[{i}]'))
        return exec_str

    def generate_inv_prime(self) -> str:
        invariants = copy.deepcopy(self.invariants)
        exec_str = [f'{inv_prime_collector_name} = []']
        for inv in invariants:
            if isinstance(inv, MurphiInvariant):
                inv_prime = inv.elaborate(self, dict(), obligation=True)
                exec_str.append(f'{prot_decl_collector_name}_{inv.name}_prime = []')
                exec_str.append(f'{inv_prime.exec_str}')
                exec_str.append(f'{inv_prime_collector_name}.extend({prot_decl_collector_name}_{inv.name}_prime)')
            else:
                assert isinstance(inv, MurphiRuleSet)
                invs = [inv_expr.elaborate(self, inv.var_map, obligation=True) for inv_expr in inv.rules]
                for_loop_str = []
                loop_cnt = 0
                for rule in invs:
                    exec_str.append(f'{prot_decl_collector_name}_{rule.name}_prime = []')
                for decl in inv.var_decls:
                    decl.elaborate(self, is_prime=True)
                    for_loop_str.append(indent(f'for {decl.name} in {decl.typ.exec_str}:', 4 * loop_cnt))
                    loop_cnt += 1
                for rule in invs:
                    exec_str.append(f'\n# rule {rule.name} of ruleset {inv.cnt}')
                    exec_str.extend(for_loop_str)
                    exec_str.append(indent(rule.exec_str, 4 * loop_cnt))
                    exec_str.append(indent(f'{inv_prime_collector_name}.extend({prot_decl_collector_name}_{rule.name}_prime)', 0))
        return '\n'.join(exec_str)

    def to_z3(self, filename):
        prot = filename.split('.')[0]

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

        # Transforming model transitions into lists with separated rule expressions
        trans_exec = f'trans = {atom_rule_collector_name}'
        inv_exec = f'post = {atom_inv_collector_name}'
        inv_prime_exec = f'{self.generate_inv_prime()}\n\npost_prime = {inv_prime_collector_name}'
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
                          f'# full vars with attributes\n'
                          f'{self.full_vars_exec_str}\n\n'
                          f'# constraints of variables\n'
                          f'{self.var_with_cons_exec_str}\n\n'
                          f'# start state declarations\n'
                          f'{self.init_exec_str}\n\n'
                          f'# invariant declarations\n'
                          f'{self.inv_exec_str}\n'
                          f'# prime invariant declarations\n'
                          f'{inv_prime_exec}\n\n'
                          f'# rule declarations\n'
                          f'{self.prot_exec_str}\n'
                          f'# get z3 expression of transitions\n'
                          f'{trans_exec}\n\n'
                          f'# get z3 expression of invariants\n'
                          f'{inv_exec}\n'
                          )
        # print(to_z3_exec_str)
        with open(f'exec_str_{prot}.py', 'w') as f:
            f.write('from z3 import *\n\n\n')
            f.write('variables = []\n')
            f.write('primes = []\n\n')
            f.write(to_z3_exec_str)
            f.write(f'\n\nprint(variables, primes, init, trans, post, post_prime)\n')
        exec(to_z3_exec_str, global_vars)
        variables = global_vars['variables']
        primes = global_vars['primes']
        init = global_vars['init']
        trans = global_vars['trans']
        post = global_vars['post']
        post_prime = global_vars['post_prime']

        full_vars = global_vars['full_vars']
        var_constraints = global_vars['var_constraints']
        with open(f'exec_str_{prot}.py', 'a') as f:
            set_option(max_depth=99999, max_lines=99999, max_args=99999)
            f.write('\'\'\'\n')
            f.write(f'variables = \n{variables}\n\n')
            f.write(f'primes = \n{primes}\n\n')
            f.write(f'init = \n{init}\n\n')
            f.write(f'trans = \n{trans}\n\n')
            f.write(f'post = \n{post}\n\n')
            f.write(f'post_prime = \n{post_prime}\n\n')
            f.write('\'\'\'\n')
        return variables, primes, init, trans, post, post_prime, full_vars, var_constraints


# trans:
#   list[ rule: And(cond, assigns, others) |
#         ruleset: list[And(cond, assigns, others)]
#   ]
#   [__prot_decl_name]
# invariant:
#   list[ inv: And(expr) |
#         ruleset: list[And(expr)]
#   ]

