import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact])
        ####################################################
        # Student code goes here

        if factq(fact.name) and fact in self.facts :
            if len(fact.supports_facts) > 0:
                i = 0
                factsupp = fact.supports_facts
                currlengthi = len(factsupp)
                while i < currlengthi:
                    if factsupp[i].asserted or factsupp[i].supported:
                        i = i + 1
                    else:
                        kb_retract(factsupp[i])
                        currlengthi = currlengthi - 1

            if len(fact.supports_rules) > 0:
                j = 0
                rulesupp = fact.supports_rules
                currlengthj = len(rulesupp)
                while j < currlengthj:
                    if not rulesupp[j].asserted and not rulesupp[j].supported:
                        kb_retract(rulesupp[j])
                        currlengthj = currlengthj - 1
                    else:
                        j = j + 1

            if fact.supported:       
                k = 0
                currlengthk = len(fact.supported_by)
                while k < currlengthk: 
                    (fact.supported_by[k]).support_facts.remove(fact)
                    currlengthk = currlengthk - 1

            if fact.asserted or len(fact.supported_by) > 1:
                fact.asserted = False
            else:
                self.facts.remove(fact)

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here

        if len(rule.lhs) < 1 or not rule.rhs:
            return

        if fact not in kb.facts:
            return

        blist = match(rule.lhs[0], fact.statement)
        if blist != False:
            fr = instantiate(rule.rhs, blist)
            if len(rule.lhs) == 1:
                newf = Fact(fr)
                kb.kb_assert(newf)
                kb.kb_add(newf)
                newf.supported_by.append(fact)
                newf.supported_by.append(rule)
                fact.supports_facts.append(newf)
                rule.supports_facts.append(newf)
            else: 
                i = 1
                updatedleft = []
                while i < (len(rule.lhs) - 1):
                    updatedleft.append(instantiate(rule.lhs[i], blist))
                newr = Rule([updatedleft, fr])
                print(newr)
                kb.kb_assert(newr)
                kb.kb_add(newr)
                newr.supported_by.append(fact)
                newr.supported_by.append(rule)
                fact.supports_rules.append(newr)
                rule.supports_rules.append(newr)
