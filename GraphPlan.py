import itertools
import sys

class PlanningGraph:
    s_0 = set()
    goal = set()
    action = []
    precond = {}
    effects = {}
    states_level = {}
    actions_level = {}
    final = 0
    output_path = []
    nl_mutex = {0: set()}
    incon_effect = {}
    interference = {}
    cn = {0:set()}
    incon_supp = {0: set()}

    def PDDL_read(self,input_file):
        print("--------------------Reading File----------------------")
        with open(input_file) as PDDL:
            text = PDDL.readlines()
        for info in text:
            if info[0:4] == "INIT":
                state_0 = info.split(":")[1].strip().split(",")
                for values in state_0:
                    if "-" in values:
                        self.s_0.add((values[1:], -1))
                    else:
                        self.s_0.add((values, 1))
                self.states_level[0] = self.s_0
                self.states_print(0)
            if info[0:4] == "GOAL":
                goal_t = info.split(":")[1].strip().split(",")
                for values in goal_t:
                    if "-" in values:
                        self.goal.add((values[1:], -1))
                    else:
                        self.goal.add((values, 1))
            if info[0:6] == "ACTION":
                action_temp = info.split(":")[1].strip().split(",")
                self.action.append(action_temp[0])
            if info[0:7] == "PRECOND":
                precond_temp = info.split(":")[1].strip().split(",")
                precond_assign = []
                for values in precond_temp:
                    if "-" in values:
                        precond_assign.append((values[1:], -1))
                    else:
                        precond_assign.append((values, 1))
                self.precond[action_temp[0]] = precond_assign
            if info[0:6] == "EFFECT":
                effect_temp = info.split(":")[1].strip().split(",")
                effect_assign = []
                for values in effect_temp:
                    if "-" in values:
                        effect_assign.append((values[1:], -1))
                    else:
                        effect_assign.append((values, 1))
                self.effects[action_temp[0]] = effect_assign

    def graph_build(self):
        print("--------------------Graph building----------------------")
        present_state = 1
        print(f"******************************",present_state,"************************************", "\n")
        while 1:
            set_of_actions = set()
            match = 1
            #-------------------------------------------ADD ACTIONS--------------------------------------------------------------#
            for actions in self.action:
                for pcond in self.precond[actions]:
                    if pcond[0] == "":
                        match = 1
                        break
                    if pcond in self.states_level[present_state-1]:
                        match = 1
                    else:
                        match = 0
                if match == 1:
                    set_of_actions.add(actions)
            # persist action
            persist_temp = []
            for st in self.states_level[present_state-1]:
                lit, value = st
                if value == 1:
                    persist_temp.append(lit)
                else:
                    var = "-"+lit
                    persist_temp.append(var)
            for p_act in persist_temp:
                set_of_actions.add(f'persist_{p_act}')
            self.actions_level[present_state] = set_of_actions
            self.actions_print(present_state)

            #----Add states to the graph--------------#
            next_state = set()
            for st in self.states_level[present_state-1]:
                next_state.add(st)

            #-----Add effects to the graph-------------#
            for actions in self.actions_level[present_state]:
                if actions[0:7] == "persist":
                    pass
                else:
                    for eff in self.effects[actions]:
                        next_state.add(eff)
            self.states_level[present_state] = next_state
            self.states_print(present_state)

            #------Check mutexes-----------------------#
            self.negatedLiteral(present_state)
            self.inconeffect(present_state)
            self.interference_m(present_state)
            self.competing_needs(present_state)
            self.inconsistent_support(present_state)

            #------Goal checking-----------------------#
            check_mutex = set().union(self.nl_mutex[present_state]).union(self.incon_supp[present_state])
            stop_flag = 0
            for temp_g1 in self.goal:
                for temp_g2 in self.goal:
                    if temp_g1 != temp_g2:
                        v1,v2 = temp_g1
                        v3,v4 = temp_g2
                        if v2 == 1:
                            g1 = v1
                        else:
                            g1 = "-" + v1
                        if v4 == 1:
                            g2 = v3
                        else:
                            g2 = "-" + v3
                        if (((g1,g2) in check_mutex) or (g2,g1) in check_mutex):
                            stop_flag = 1
                            break
                        else:
                            stop_flag = 0
                if stop_flag == 1:
                    break
            if stop_flag == 0:
                self.final = present_state
                break
            present_state = present_state + 1
            print(f"******************************",present_state,"************************************", "\n")

    def backtrack(self, goal, state):
        if state < 0:
            return False
        elif state == 0:
            for each_goal in goal:
                if each_goal in self.states_level[0]:
                    path = True
                else:
                    path = False
                    break
            if path == True:
                return True
        curr_mutex = set().union(
            self.incon_effect[state], self.interference[state], self.cn[state])
        nm_p_actions = []
        for goals in goal:
            p_actions = set()
            for actions in self.actions_level[state]:
                if actions[0:8] == "persist_":
                    eff_temp = actions[8:]
                    if "-" in eff_temp:
                        eff_temp_tup = (eff_temp[1:], -1)
                    else:
                        eff_temp_tup = (eff_temp, 1)
                    if eff_temp_tup == goals:
                        p_actions.add(actions)
                else:
                    if goals in self.effects[actions]:
                        p_actions.add(actions)
            nm_p_actions.append(p_actions)
        final_list = list(itertools.product(*nm_p_actions))
        actions_nm = []
        for action_r in final_list:
            comb_two = []
            check_in_mutex = False
            for i in action_r:
                for j in action_r:
                    if i != j and ((j, i) not in comb_two) and ((i, j) not in comb_two):
                        comb_two.append((i, j))
            for combos in comb_two:
                value_1, value_2 = combos
                if ((value_1, value_2) in curr_mutex) or ((value_2, value_1) in curr_mutex):
                    check_in_mutex = False
                    break
                else:
                    check_in_mutex = True
            if check_in_mutex:
                actions_nm.append(tuple(set(action_r)))
        if not actions_nm:
            return False
        precon_nm = []
        for actions_nma in actions_nm:
            self.output_path.append(actions_nma)
            precon_temp = set()
            for each_act in actions_nma:
                if each_act[0:8] == "persist_":
                    if "-" in each_act:
                        precon_temp.add((each_act[9:],-1))
                    else:
                        precon_temp.add((each_act[8:],1))
                else:
                    for precon_1 in self.precond[each_act]:
                        if precon_1[0] == "":
                            pass
                        else:
                            precon_temp.add(precon_1)
            precon_nm.append(precon_temp)
            next_goal = precon_nm[0]
            if self.backtrack(next_goal,state-1):
                return True
            else:
                self.output_path.remove(actions_nma)
                return False

    def negatedLiteral(self, state):
        nl_mutex_temp = set()
        current_state = self.states_level[state]
        for key in current_state:
            i, j = key
            if (i, -j) in current_state:
                nl_mutex_temp.add((i, "-"+str(i)))
        self.nl_mutex[state] = nl_mutex_temp
        print("NL at state ", state)
        print(self.nl_mutex[state], "\n")

    def inconeffect(self, state):
        current_action = self.actions_level[state]
        ie_mutex_temp = set()
        for actions in current_action:
            if actions[0:8] == "persist_":
                effects_t = actions[8:]
                if "-" in effects_t:
                    effects = (effects_t[1:], -1)
                else:
                    effects = (effects_t, 1)
                for actions_1 in current_action:
                    if actions_1[0:8] == "persist_":
                        pass
                    else:
                        for effects_itr in self.effects[actions_1]:
                            if effects_itr[0] == effects[0] and effects_itr[1] == -effects[1]:
                                if (actions_1, actions) not in ie_mutex_temp:
                                    ie_mutex_temp.add((actions, actions_1))
            else:
                for effects_1, actions_2 in itertools.product(self.effects[actions], current_action):
                    if actions_2[0:8] == "persist_":
                        pass
                    else:
                        for effects_2 in self.effects[actions_2]:
                            if effects_1[0] == effects_2[0] and effects_1[1] == -effects_2[1]:
                                if(actions_2, actions) not in ie_mutex_temp:
                                    ie_mutex_temp.add((actions, actions_2))
        self.incon_effect[state] = ie_mutex_temp
        print("Inconsistent effect mutex at action ", state)
        print(self.incon_effect[state], "\n")

    def interference_m(self, state):
        current_action = self.actions_level[state]
        it_mutex_temp = set()
        for actions in current_action:
            if actions[0:8] == "persist_":
                precond_t = actions[8:]
                if "-" in precond_t:
                    precon = (precond_t[1:], -1)
                else:
                    precon = (precond_t, 1)
                for actions_1 in current_action:
                    if actions_1[0:8] == "persist_":
                        pass
                    else:
                        for precon_itr in self.precond[actions_1]:
                            if precon_itr[0] == precon[0] and precon_itr[1] == -precon[1]:
                                if (actions_1, actions) not in it_mutex_temp:
                                    it_mutex_temp.add((actions, actions_1))
            else:
                for precon_1 in self.effects[actions]:
                    for actions_2 in current_action:
                        if actions_2[0:8] == "persist_":
                            pass
                        else:
                            for precon_2 in self.precond[actions_2]:
                                if precon_1[0] == precon_2[0] and precon_1[1] == -precon_2[1]:
                                    if((actions_2, actions) not in it_mutex_temp) and (actions_2 != actions):
                                        it_mutex_temp.add((actions, actions_2))
        self.interference[state] = it_mutex_temp
        print("Interference mutex at action ", state)
        print(self.interference[state], "\n")

    def competing_needs(self, state):
        set_mutex = set()
        comp_needs = set()
        action_mutex = self.nl_mutex[state-1].union(self.incon_supp[state-1])
        for m_actions in action_mutex:
            temp_m_actions = []
            for m_ac in m_actions:
                if "-" in m_ac:
                    temp_m_actions.append((m_ac[1:], -1))
                else:
                    temp_m_actions.append((m_ac, 1))
            set_mutex.add(tuple(temp_m_actions))
        for action_1 in self.actions_level[state]:
            first_action = set()
            if action_1[0:8] == "persist_":
                first_action_temp = action_1[8:]
                if "-" in first_action_temp:
                    first_action.add((first_action_temp[1:], -1))
                else:
                    first_action.add((first_action_temp, 1))
            else:
                for precond_1 in self.precond[action_1]:
                    first_action.add(precond_1)

            for action_2 in self.actions_level[state]:
                second_action = set()
                if action_1 != action_2:
                    if action_2[0:8] == "persist_":
                        second_action_temp = action_2[8:]
                        if "-" in second_action_temp:
                            second_action.add((second_action_temp[1:], -1))
                        else:
                            second_action.add((second_action_temp, 1))
                    else:
                        for precond_2 in self.precond[action_2]:
                            second_action.add(precond_2)
                else:
                    continue
                for ac1, ac2 in itertools.product(first_action, second_action):
                    if ac1 != ac2:
                        if ((ac1, ac2) in set_mutex) or ((ac2, ac1) in set_mutex):
                            if (action_2, action_1) not in comp_needs:
                                comp_needs.add((action_1, action_2))
        self.cn[state] = comp_needs
        print("Competent need mutex at action ", state)
        print(self.cn[state], "\n")

    def inconsistent_support(self, state):
        if state > 1:
            all_mutex = set().union(
                self.incon_effect[state], self.interference[state], self.cn[state])
        else:
            all_mutex = set().union(
                self.incon_effect[state], self.interference[state])
        incon_supp_t = set()
        for states in self.states_level[state]:
            first_action = set()
            literal, value = states
            if value == 1:
                og_literal = literal
            if value == -1:
                og_literal = "-" + literal
            for action_is in self.actions_level[state]:
                if action_is[0:8] == "persist_":
                    if action_is[8:] == og_literal:
                        first_action.add(action_is)
                else:
                    if states in self.effects[action_is]:
                        first_action.add(action_is)
            for states_1 in self.states_level[state]:
                second_action = set()
                if (states[0] == states_1[0]):
                    if states[1] == -states_1[1] or states[1] == states_1[1]:
                        continue
                else:
                    literal1, value1 = states_1
                    if value1 == 1:
                        og_literal_1 = literal1
                    if value1 == -1:
                        og_literal_1 = "-" + literal1
                    for action_is_1 in self.actions_level[state]:
                        if action_is_1[0:8] == "persist_":
                            if action_is_1[8:] == og_literal_1:
                                second_action.add(action_is_1)
                        else:
                            if states_1 in self.effects[action_is_1]:
                                second_action.add(action_is_1)
                check_in_mutex = 0
                for action1 in first_action:
                    for action2 in second_action:
                        if (action1, action2) in all_mutex:
                            check_in_mutex = 1
                        elif (action2, action1) in all_mutex:
                            check_in_mutex = 1
                        else:
                            check_in_mutex = 0
                            break
                    if not check_in_mutex:
                        break
                if check_in_mutex:
                    if (og_literal_1, og_literal) not in incon_supp_t:
                        incon_supp_t.add((og_literal, og_literal_1))
        self.incon_supp[state] = incon_supp_t
        print("Inconsistent support mutex at state ", state)
        print(self.incon_supp[state], "\n")

    def states_print(self, state):
        print("state", state)
        p_list = []
        for states_p in self.states_level[state]:
            x, y = states_p
            if y == -1:
                p_list.append("-"+x)
            else:
                p_list.append(x)
        print(p_list, "\n")

    def actions_print(self, state):
        if state == 0:
            pass
        else:
            print("action", state)
            a_list = []
            for actions_p in self.actions_level[state]:
                a_list.append(actions_p)
            print(a_list, "\n")


#----------Initiating the process-----------------------#
obj = PlanningGraph()
input_file = str(sys.argv[1])
obj.PDDL_read(input_file)
obj.graph_build()
print("--------------------Finding Path----------------------")
if obj.backtrack(obj.goal, obj.final):
    rev_list = reversed(obj.output_path)
    final_output=[]
    for i in rev_list:
        final_output.append(i)
    print("The final path for goal is",final_output)
else:
    print("No path found")
