from murphiparser import parse_file
from pdr import PDR
from murphi import *
from z3 import *


class AtomAssign:
    def __init__(self, left_val: str, right_val: BaseExpr, is_prime: bool = False):
        self.left_val = left_val
        self.right_val = right_val
        self.is_prime = is_prime

    def get_lval(self):
        return self.left_val + '\'' if self.is_prime else self.left_val

    def get_rval(self):
        return self.right_val

    def __repr__(self):
        return f'{self.get_lval()} = {self.get_rval()}'


# noinspection PyShadowingNames
class Murphi2Protocol:
    def __init__(self, path):
        self.path: str = path
        self.prot: MurphiProtocol = parse_file(path)

        self.const_map: dict[str, MurphiConstDecl] = {const.name: const for const in self.prot.consts}
        self.typ_map: dict[str, MurphiType] = self.prot.typ_map
        self.var_map: dict[str, MurphiType] = self.prot.var_map

        self.ruleset_map: dict[str, MurphiRuleSet] = self.prot.rule_map

        self.z3_typ: dict[str, list[DatatypeSortRef | dict[str, AstRef] | int]] = {}
        self.z3_var: dict[str, AstRef] = {}
        self.z3_var_prime: dict[str, AstRef] = {}

        self.murphi2z3_typ: dict[MurphiType, str] = {}

    def elaborate_types_init(self):
        for name, typ in self.typ_map.items():
            if isinstance(typ, BooleanType):
                pass
            elif isinstance(typ, ScalarSetType):
                bound = int(self.const_map[typ.const_name].val)
                self.z3_typ[name] = list(range(1, bound+1))
                self.murphi2z3_typ[typ] = name
            elif isinstance(typ, UnionType):
                pass
            elif isinstance(typ, EnumType):
                state, vals = EnumSort(name, typ.names)
                self.z3_typ[name] = [state, {enum_name: enum_z3_val for enum_name, enum_z3_val in zip(typ.names, vals)}]
                self.murphi2z3_typ[typ] = name
            elif isinstance(typ, ArrayType):
                pass
            elif isinstance(typ, RecordType):
                pass
            else:
                raise NotImplementedError

    def elaborate_vars_init(self):
        for name, typ in self.var_map.items():
            if isinstance(typ, BooleanType):
                self.z3_var[name] = Bool(name)
                self.z3_var_prime[name] = Bool(f'{name}\'')
            elif isinstance(typ, ScalarSetType):
                pass
            elif isinstance(typ, UnionType):
                pass
            elif isinstance(typ, EnumType):
                pass
            elif isinstance(typ, ArrayType):
                match typ.ele_typ:
                    case t if isinstance(t, VarType):
                        element_class: DatatypeSortRef = self.z3_typ[t.name][0]
                    case _:
                        raise NotImplementedError
                match typ.idx_typ:
                    case i if isinstance(i, VarType):
                        index_range = self.z3_typ[i.name]
                    case _:
                        raise NotImplementedError

                element_names = [f'{name}[{i}]' for i in index_range]
                z3_consts = Consts(' '.join(element_names), element_class)
                for var_name, z3_const in zip(element_names, z3_consts):
                    self.z3_var[var_name] = z3_const

                element_names_prime = [f'{name}\'[{i}]' for i in index_range]
                z3_consts_prime = Consts(' '.join(element_names_prime), element_class)
                for var_name, z3_const in zip(element_names_prime, z3_consts_prime):
                    self.z3_var_prime[var_name] = z3_const
            elif isinstance(typ, RecordType):
                pass
            else:
                raise NotImplementedError

    def elaborate_ruleset_types(self, ):
        pass

    def elaborate_ruleset_vars(self, ruleset_var_map: dict[str, MurphiType]) -> dict[str, list[int]]:
        typ_dict = {}
        for name, typ in ruleset_var_map.items():
            if isinstance(typ, VarType):
                assert typ.name in self.z3_typ
                typ_dict[name] = self.z3_typ[typ.name]
            else:
                raise NotImplementedError
        return typ_dict

    def elaborate_fields_recursive(self, field: FieldName) -> list[str]:
        match field.v:
            case v if isinstance(v, VarExpr):
                return [f'{v.name}_{field.field}']
            case v if isinstance(v, FieldName):
                return [f'{v_name}_{field.field}' for v_name in self.elaborate_fields_recursive(v)]
            case v if isinstance(v, ArrayIndex):
                pass
            case _:
                raise NotImplementedError

    def elaborate_array_index_recursive(self, array: ArrayIndex,
                                        decls: dict[str, MurphiVarDecl] = None
                                        ) -> list[str]:
        match array.v:
            case v if isinstance(v, VarExpr):
                var_names = [f'{v.name}']
            case v if isinstance(v, FieldName):
                var_names = f'{self.elaborate_fields_recursive(v)}'
            case v if isinstance(v, ArrayIndex):
                var_names = self.elaborate_array_index_recursive(v, decls)
            case _:
                raise NotImplementedError
        match array.idx:
            case i if isinstance(i, VarExpr):
                if i.name in decls:
                    decl = decls[i.name]
                    typ = decl.typ
                    assert typ.name in self.typ_map
                    i_scope: list[int] = self.z3_typ[typ.name]
                    return [f'{var_name}[{i}]' for i in i_scope for var_name in var_names]
                else:
                    raise NotImplementedError
            case _:
                raise NotImplementedError

    def traverse_cmds_recursive(self,
                                cmds: list[BaseCmd],
                                decls: dict[str, MurphiVarDecl] = None,
                                is_prime: bool = False
                                ) -> list[AtomAssign]:
        if decls is None:
            decls = {}
        assigns = []
        for cmd in cmds:
            match cmd:
                case _ if isinstance(cmd, UndefineCmd):
                    raise NotImplementedError
                case c if isinstance(c, AssignCmd):
                    match c.var:
                        case v if isinstance(v, VarExpr):
                            assert v.name in self.var_map
                            assigns.append(AtomAssign(v.name, c.expr, is_prime))
                        case v if isinstance(v, FieldName):
                            pass
                        case v if isinstance(v, ArrayIndex):
                            var_names = self.elaborate_array_index_recursive(v, decls)
                            for var_name in var_names:
                                assigns.append(AtomAssign(var_name, c.expr, is_prime))
                case c if isinstance(c, ForallCmd):
                    assigns += self.traverse_cmds_recursive(c.cmds, decls | {c.var_decl.name: c.var_decl})
                case _ if isinstance(cmd, IfCmd):
                    raise NotImplementedError
                case _:  # Not implemented
                    raise NotImplementedError
        return assigns

    def elaborate_cond(self, cond: BaseExpr, decls: dict[str, MurphiVarDecl] = None) -> AstRef | bool:
        if decls is None:
            decls = {}
        if isinstance(cond, VarExpr):
            return self.z3_var[cond.name]
        elif isinstance(cond, EnumValExpr):
            typ_name = self.murphi2z3_typ[cond.enum_type]
            z3_enum_dict = self.z3_typ[typ_name][1]
            return z3_enum_dict[cond.enum_val]
        elif isinstance(cond, FieldName):
            raise NotImplementedError
        elif isinstance(cond, ArrayIndex):
            pass
        elif isinstance(cond, BooleanExpr):
            return cond.val
        elif isinstance(cond, OpExpr):
            left_val = self.elaborate_cond(cond.expr1, decls)
            right_val = self.elaborate_cond(cond.expr2, decls)
            assert left_val is not None and right_val is not None
            match cond.op:
                case '+':
                    raise NotImplementedError
                case '-':
                    raise NotImplementedError
                case '*':
                    raise NotImplementedError
                case '/':
                    raise NotImplementedError
                case '%':
                    raise NotImplementedError
                case '<=':
                    raise NotImplementedError
                case '>=':
                    raise NotImplementedError
                case '<':
                    raise NotImplementedError
                case '>':
                    raise NotImplementedError
                case '=':
                    return left_val == right_val
                case '!=':
                    return left_val != right_val
                case '&':
                    return And(left_val, right_val)
                case '|':
                    return Or(left_val, right_val)
                case '->':
                    return Implies(left_val, right_val)
                case _:
                    raise NotImplementedError
        elif isinstance(cond, NegExpr):
            return Not(self.elaborate_cond(cond.expr, decls))
        else:
            raise NotImplementedError

    def elaborate_ruleset(self, ruleset: MurphiRuleSet) -> list[BoolRef]:
        # typ_dict = self.elaborate_ruleset_vars(ruleset.var_decls)
        cond: BoolRef | bool = self.traverse_cmds_recursive([ruleset.rule.cond], ruleset.var_decls)
        if isinstance(cond, bool) and not cond:
            return []
        assigns = self.traverse_cmds_recursive(ruleset.rule.cmds, ruleset.var_decls, is_prime=True)
        # PRIME Z3 VARS
        z3_exprs = []
        for assign in assigns:
            left_val = assign.get_lval()
            right_val = assign.get_rval()
            assert left_val in self.z3_var_prime
            match right_val:
                case v if isinstance(v, BooleanExpr):
                    z3_exprs.append(self.z3_var_prime[left_val] if v.val else Not(self.z3_var_prime[left_val]))
                case v if isinstance(v, EnumValExpr):
                    typ_name = self.murphi2z3_typ[v.enum_type]
                    z3_enum_dict = self.z3_typ[typ_name][1]
                    z3_exprs.append(self.z3_var_prime[left_val] == z3_enum_dict[v.enum_val])
                case _:
                    raise NotImplementedError
        return And(*z3_exprs)

    def get_init(self) -> BoolRef:
        start_state: [StartState | RulesetStartState] = self.prot.start_state
        assigns = self.traverse_cmds_recursive(start_state.cmds) if isinstance(start_state, StartState) \
            else self.traverse_cmds_recursive(start_state.startstate.cmds, start_state.var_decls)
        z3_exprs = []
        for assign in assigns:
            left_val = assign.get_lval()
            right_val = assign.get_rval()
            assert left_val in self.z3_var
            match right_val:
                case v if isinstance(v, BooleanExpr):
                    z3_exprs.append(self.z3_var[left_val] if v.val else Not(self.z3_var[left_val]))
                case v if isinstance(v, EnumValExpr):
                    typ_name = self.murphi2z3_typ[v.enum_type]
                    z3_enum_dict = self.z3_typ[typ_name][1]
                    z3_exprs.append(self.z3_var[left_val] == z3_enum_dict[v.enum_val])
                case _:
                    raise NotImplementedError
        return And(*z3_exprs)

    def get_trans(self) -> BoolRef:
        return Or(*[self.elaborate_ruleset(rule) for rule in self.ruleset_map.values()])

    def pdrInterface(self):
        self.elaborate_types_init()
        self.elaborate_vars_init()
        variables_pdr = self.z3_var.values()
        primes_pdr = self.z3_var_prime.values()
        init_pdr = self.get_init()
        trans_pdr = self.get_trans()
        inv_pdr = []

        return variables_pdr, primes_pdr, init_pdr, trans_pdr, inv_pdr


def murphi(path):
    parser = Murphi2Protocol(path)
    return parser.pdrInterface()


if __name__ == "__main__":
    # file_path = '/home/loyce/MC/paraVerifier/murphi2ocaml/murphi/flash.m'
    file_path = 'mutualEx.m'
    print("=========== Running Murphi PDR ===========")
    murphi_test = murphi(file_path)
    solver = PDR(*murphi_test)
    solver.run()
