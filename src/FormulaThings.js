function union(set1, set2) {
    output = new Set();
    set1.forEach(elt => {
        output.add(elt);
    });
    set2.forEach(elt => {
        output.add(elt);
    });
    return output
}

function duplicate(set) {
    output = new Set();
    set.forEach(elt => {
        output.add(elt);
    });
    return output;
}

function formulaToString(formula) {
    switch (formula.type) {
        case "equals":
            return formula.v1 + " = " + formula.v2;
        case "in":
            return formula.v1 + " \u2208 " + formula.v2;
        case "and":
            return "(" + formulaToString(formula.f1) + ") \u2227 (" + formulaToString(formula.f2) + ")";
        case "or":
            return "(" + formulaToString(formula.f1) + ") \u2228 (" + formulaToString(formula.f2) + ")";
        case "implies":
            return "(" + formulaToString(formula.f1) + ") \u2192 (" + formulaToString(formula.f2) + ")";
        case "exists":
            return "(\u2203" + formula.v + ")(" + formulaToString(formula.f) + ")"
        case "all":
            return "(\u2200" + formula.v + ")(" + formulaToString(formula.f) + ")"
        case "not":
            return "\u00ac" + "(" + formulaToString(formula.f) + ")"
    }
}

Formula = {
    equals: function (v1, v2) {
        vars = new Set()
        vars.add(v1);
        vars.add(v2);
        output = {
            type: "equals",
            v1: v1,
            v2: v2,
            vars: vars,
            replacevars: function (oldvar, newvar) {
                stringForm = v1 + " = " + v2;
                return interpretSentence(stringForm.split(oldvar).join(newvar));
            }
        };
        return output;

    },
    in: function (v1, v2) {
        vars = new Set()
        vars.add(v1);
        vars.add(v2);
        output = {
            type: "in",
            v1: v1,
            v2: v2,
            vars: vars,
            replacevars: function (oldvar, newvar) {
                stringForm = v1 + " \u2208 " + v2;
                return interpretSentence(stringForm.split(oldvar).join(newvar));
            }
        };
        return output;
    },
    and: function (f1, f2) {
        return {
            type: "and",
            f1: f1,
            f2: f2,
            vars: union(f1.vars, f2.vars),
            replacevars: function (oldvar, newvar) {
                return Formula.and(
                    f1.replacevars(oldvar, newvar),
                    f2.replacevars(oldvar, newvar),
                );
            },
        };
    },
    or: function (f1, f2) {
        return {
            type: "or",
            f1: f1,
            f2: f2,
            vars: union(f1.vars, f2.vars),
            replacevars: function (oldvar, newvar) {
                return Formula.or(
                    f1.replacevars(oldvar, newvar),
                    f2.replacevars(oldvar, newvar),
                );
            },
        };
    },
    implies: function (f1, f2) {
        return {
            type: "implies",
            f1: f1,
            f2: f2,
            vars: union(f1.vars, f2.vars),
            replacevars: function (oldvar, newvar) {
                return Formula.implies(
                    f1.replacevars(oldvar, newvar),
                    f2.replacevars(oldvar, newvar),
                );
            },
        };
    },
    exists: function (f, variable) {
        vars = duplicate(f.vars);
        vars.delete(variable);
        return {
            type: "exists",
            f: f,
            v: variable,
            vars: vars,
            replacevars: function (oldvar, newvar) {
                if (variable == oldvar) {
                    return Formula.exists(f.replacevars(oldvar, newvar), newvar);
                }
                return Formula.exists(f.replacevars(oldvar, newvar), variable);
            },
        };
    },
    all: function (f, variable) {
        vars = duplicate(f.vars);
        vars.delete(variable);
        return {
            type: "all",
            f: f,
            v: variable,
            vars: vars,
            replacevars: function (oldvar, newvar) {
                if (variable == oldvar) {
                    return Formula.all(f.replacevars(oldvar, newvar), newvar);
                }
                return Formula.all(f.replacevars(oldvar, newvar), variable);
            },
        };
    },
    not: function (f) {
        if (f.type == "not") {
            return f.f;
        }
        return {
            type: "not",
            f: f,
            vars: f.vars,
            replacevars: function (oldvar, newvar) {
                return Formula.not(f.replacevars(oldvar, newvar));
            },
        };
    },
    isSentence: function (f) {
        return f.vars == Set();
    },
    matches: function (f1, f2) {
        return formulaToString(f1) == formulaToString(f2);
    }
}

function interpretSentence(inputString) {
    if (!inputString.includes("(")) {
        if (inputString.includes("=")) {
            return Formula.equals(...inputString.split(" ").join("").split("="));
        }
        if (inputString.includes("\u2208")) {
            return Formula.in(...inputString.split(" ").join("").split("\u2208"));
        }
        throw new Error("Not valid formula");
    }
    var parts = decomposeByParenthises(inputString);
    if (parts[0].includes("\u00ac")) {
        return Formula.not(interpretSentence(parts[1]));
    }
    if (parts[2].includes("\u2227")) {
        return Formula.and(interpretSentence(parts[1]), interpretSentence(parts[3]));
    }
    if (parts[2].includes("\u2228")) {
        return Formula.or(interpretSentence(parts[1]), interpretSentence(parts[3]));
    }
    if (parts[2].includes("\u2192")) {
        return Formula.implies(interpretSentence(parts[1]), interpretSentence(parts[3]));
    }
    var quantifier = parts[1].split(" ").join("")[0];
    var variable = parts[1].split(" ").join("").slice(1);
    if (quantifier == "\u2203") {
        return Formula.exists(interpretSentence(parts[3]), variable);
    }
    if (quantifier == "\u2200") {
        return Formula.all(interpretSentence(parts[3]), variable);
    }
    throw new Error("not valid formula");

}

function decomposeByParenthises(inputString) {
    var leftMinusRight = 0;
    var parts = [];
    var currentPart = "";
    for (var i = 0; i < inputString.length; i++) {
        if (inputString[i] == "(" && leftMinusRight == 0) {
            parts.push(currentPart);
            currentPart = "";
        } else if (inputString[i] == ")" && leftMinusRight == 1) {
            parts.push(currentPart);
            currentPart = "";
        } else {
            currentPart += inputString[i];
        }
        if (inputString[i] == "(") {
            leftMinusRight += 1
        }
        if (inputString[i] == ")") {
            leftMinusRight -= 1
        }
        
    }
    parts.push(currentPart);
    return parts.slice();
}

function matchParens(string) {
    var leftMinusRight = 0;
    for (var i = 0; i < string.length; i++) {
        if (string[i] == "(") {
            leftMinusRight += 1
        }
        if (string[i] == ")") {
            leftMinusRight -= 1
        }
        if (leftMinusRight < 0) {
            return false;
        }

    }
    return leftMinusRight == 0;
}

