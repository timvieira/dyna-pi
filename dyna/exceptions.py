class PlanningFailure(Exception):
    pass

class SolverLimitation(Exception):
    pass

class InstFault(Exception):
    pass

class AggregatorMismatch(Exception):
    pass

class DynaParserException(Exception):
    pass

class ViolatedInvariant(Exception):
    pass

class Fatal(Exception):
    pass

class AggregatorValueError(Exception):
    pass

class OverBudget(Exception):
    pass

class NotBuiltin(Exception):
    pass
