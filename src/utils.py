# Protocol Level
# list[
#   Invariant: prot_decl_collector_name
#   RuleSet: ruleset_collector_cnt
# ]
atom_inv_collector_name = '__atom_invs'
inv_prime_collector_name = '__inv_prime'

# RuleSet Level
# list[prot_decl_collector_name]
ruleset_init_collector_name = '__ruleset_init'
atom_rule_collector_name = '__atom_rules'
rule_cmds_collector_name = '__rule_cmds'
rule_others_collector_name = '__rule_others'

for_cmd_collector_name = '__for_cmds'
for_cmd_used_var_collector_name = '__for_cmd_used_vars'

if_cmd_collector_name = '__if_cmds'
if_cmd_used_var_collector_name = '__if_cmd_used_vars'
branch_collector_name = '__if_branch'
branch_used_var_collector_name = '__if_branch_used_vars'

for_expr_collector_name = '__for_exprs'
prot_decl_collector_name = '__prot_decls'
rule_used_var_collector_name = '__rule_used_vars'
obligation_collector_name = '__obligation'


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
