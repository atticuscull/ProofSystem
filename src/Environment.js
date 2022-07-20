function Constant(label, type, trait = undefined) {
    this.label = label;
    this.type = type;
    this.trait = trait;
}

function Statement(sentence, label) {
    this.sentence = sentence;
    this.label = label;
    this.proof = {
        type: "",
        arguments: undefined,
    };
}

function Environment(parent = undefined, label = undefined) {
    this.label = parent ? label : "main";
    this.parent = parent;
    this.statements = {};
    this.environments = {};
    this.constants = {};
    this.assumptions = [];
    this.addAssumption = function (sentence, label) {
        newStatement = new Statement(sentence, label);
        newStatement.proof.type = "Asumption";        
        this.assumptions.push(newStatement);
        this.addStatement(newStatement);
        return newStatement;
    }
    this.createSubEnvironment = function (label) {
        if (this.environments[label] != undefined) {
            throw new Error("an environment with that label already exists");
        }
        newEnvironment = new Environment(this, label);
        this.environments[label] = newEnvironment;
    }
    this.getDependencies = function (reference) {
        var path = reference.split("\\");
        path.reverse();
        var output = [];
        var thisEnvironment = this;
        while (path.length > 1) {
            thisEnvironment = thisEnvironment.environments[path.pop()]
            output.push(...thisEnvironment.assumptions);
        }
        return output;
    }
    this.statementIsInContext = function (label, searchDirection = "both") {
        var output = this.statements[label] != undefined;
        if (searchDirection == "up" || searchDirection == "both") {
            if (this.parent != undefined) {
                output ||= this.parent.statementIsInContext(label, "up");
            }
        }
        if (searchDirection == "down" || searchDirection == "both") {
            Object.values(this.environments).forEach(e => {
                output ||= e.statementIsInContext(label, "down");
            });
        }
        return output;
    }
    this.constantIsInContext = function(label, searchDirection = "both") {
        var output = this.constants[label] != undefined;
        if (searchDirection == "up" || searchDirection == "both") {
            if (this.parent != undefined) {
                output ||= this.parent.constantIsInContext(label, "up");
            }
        }
        if (searchDirection == "down" || searchDirection == "both") {
            Object.values(this.environments).forEach(e => {
                output ||= e.constantIsInContext(label, "down");
            });
        }
        return output;    
    }
    this.addStatement = function (statement) {
        var label = statement.label;
        if (!this.statementIsInContext(label)) {
            this.statements[label] = statement;
        } else {
            throw new Error("a statement with that label is already in context");
        }
    }
    this.addConstant = function (constant) {
        var label = constant.label;
        if (!this.constantIsInContext(label)) {
            this.constants[label] = constant;
        } else {
            throw new Error("a constant with that label is already in context");
        }
    }
    this.getStatement = function (reference, restriction = "none") {
        var path = reference.split("\\");
        var statementLabel = path.pop();
        var environment = (path.length == 0) ? this : this.getEnvironmentFromRef(path.join("\\"), restriction);
        var output = environment.statements[statementLabel];
        if (output == undefined) {
            throw new Error("invalid Statement reference");
        }
        return output;
    }
    this.getConstant = function (reference, restriction = "none") {
        console.log(reference)
        var path = reference.split("\\");
        var constantLabel = path.pop();
        var environment = (path.length == 0) ? this : this.getEnvironmentFromRef(path.join("\\"), restriction);
        var output = environment.constants[constantLabel];
        if (output == undefined) {
            throw new Error("invalid Statement reference");
        }
        return output;
    }
    this.getLabeledStatement = function (label) {
        var thisEnvironment = this;
        while (thisEnvironment != undefined) {
            if (thisEnvironment.statements[label] != undefined) {
                return thisEnvironment.statements[label];
            }
            thisEnvironment = thisEnvironment.parent;
        }
        return undefined;
    }
    this.getLabeledConstant = function (label) {
        var thisEnvironment = this;
        while (thisEnvironment != undefined) {
            if (thisEnvironment.constants[label] != undefined) {
                return thisEnvironment.constants[label];
            }
            thisEnvironment = thisEnvironment.parent;
        }
        return undefined;
    }
    this.getEnvironmentFromRef = function (reference, restriction = "none") {
        var path = reference.split("\\");
        path.reverse();
        var thisEnvironment = this;
        while (path.length > 0) {
            nextEnvironmentLabel = path.pop();
            if (nextEnvironmentLabel == "<") {
                if (restriction == "onlyDown") {
                    throw new Error("reference doesn't follow restrictions");
                }
                thisEnvironment = thisEnvironment.parent
            } else {
                if (restriction == "onlyUp") {
                    throw new Error("reference doesn't follow restrictions");
                }
                thisEnvironment = thisEnvironment.environments[nextEnvironmentLabel];
                if (thisEnvironment == undefined) {
                    throw new Error("invalid Environment reference");
                }
            }
        }
        return thisEnvironment;
    }
    this.getReferenceFromUpwardEnvironment = function(reference, environment) {
        var path = reference.split("\\");
        var label = path.pop();
        var prefix = "";
        thisEnvironment = this;
        while (thisEnvironment != environment) {
            if (path.length > 0) {
                path.pop();
            } else {
                prefix = thisEnvironment.label + "\\" + prefix;
            }
            thisEnvironment = thisEnvironment.parent;
        }
        return prefix + path.join("\\") + "\\" + label;
    }
    this.squash = function (reference, newLabel) {
        var dependencies = this.getDependencies(reference);
        var environment = this.getEnvironmentFromRef(reference.split("\\").slice(0, -1).join("\\"), "onlyDown");
        var statement = this.getStatement(reference, "onlyDown");
        if (dependencies.length == 0) {
            var sentence = statement.sentence;
        } else if (dependencies.length == 1) {
            var sentence = Formula.implies(
                dependencies[0].sentence,
                statement.sentence
            );
        } else {
            var conjunction = Formula.and(
                dependencies.pop().sentence,
                dependencies.pop().sentence
            );
            while (dependencies.length > 0) {
                conjunction = Formula.and(
                    conjunction,
                    dependencies.pop().sentence
                )
            }
            var sentence = Formula.implies(
                conjunction,
                statement.sentence
            );
        }

        var freeVars = [];
        var definedVars = [];
        sentence.vars.forEach(variable => {
            var constant = environment.getLabeledConstant(variable);
            if (!this.constantIsInContext(variable, "up")) {
                if (constant.type == "free") {
                    freeVars.push(variable);
                } else {
                    definedVars.push(variable);
                }
            }
        });

        while (freeVars.length > 0) {
            sentence = Formula.all(sentence, freeVars.pop());
        }

        while (definedVars.length > 0) {
            sentence = Formula.exists(sentence, definedVars.pop());
        }

        var squashedStatement = new Statement(
            sentence,
            newLabel
        );
        squashedStatement.proof.type = "squash";
        squashedStatement.proof.arguments = reference;
        this.addStatement(squashedStatement);
    }
    this.and = function (ref1, ref2, newLabel) {
        var sentence1 = this.getLabeledStatement(ref1).sentence;
        var sentence2 = this.getLabeledStatement(ref2).sentence;
        var newStatement = new Statement(
            Formula.and(sentence1, sentence2),
            newLabel
        );
        newStatement.proof.type = "and";
        newStatement.proof.arguments = [ref1, ref2];
        this.addStatement(newStatement);
    }
    this.contrapositive = function (reference, label) {
        var statement = this.getLabeledStatement(reference);
        if (statement.sentence.type != "implies") {
            throw new Error("not implication statement");
        }
        var newStatement = new Statement(
            Formula.implies(
                Formula.not(statement.sentence.f2),
                Formula.not(statement.sentence.f1),
            ),
            label
        );
        newStatement.proof.type = "contra";
        newStatement.proof.arguments = reference;
        this.addStatement(newStatement);
    }
    this.impliesTrue = function (reference, sentence, label) {
        var newStatement = new Statement(
            Formula.implies(
                sentence,
                this.getLabeledStatement(reference).sentence,
            ),
            label
        );
        newStatement.proof.type = "impTrue";
        newStatement.proof.arguments = reference;
        this.addStatement(newStatement);
    }
    this.modusPonens = function (ref1, ref2, label) {
        var statement1 = this.getLabeledStatement(ref1);
        var statement2 = this.getLabeledStatement(ref2);
        if (statement2.sentence.type != "implies") {
            throw new Error("not implication");
        }
        if (!Formula.matches(statement2.sentence.f1, statement1.sentence)) {
            throw new Error("statement and hypothesis don't match");
        }
        newStatement = new Statement(
            statement2.sentence.f2,
            label
        );
        newStatement.proof.type = "modusPonens";
        newStatement.proof.argument = [ref1, ref2];
        this.addStatement(newStatement);
    }
    this.getPath = function () {
        output = this.label;
        thisEnvironment = this;
        while (thisEnvironment.parent != undefined) {
            thisEnvironment = thisEnvironment.parent;
            output = thisEnvironment.label + "\\" + output;
        }
        return output;
    }
    this.matchAssumption = function (label, reference) {
        var parentStatement = this.getStatement(reference);
        var labeledStatement = this.statements[label];
        if (Formula.matches(parentStatement.sentence, labeledStatement.sentence)) {
            labeledStatement.proof.type = "borrowing"
            labeledStatement.proof.arguments = reference;
        }
    }
    this.addConstantFromExistential = function (reference, label, definingTraitLabel) {
        var existential = this.getLabeledStatement(reference);
        if (existential.sentence.type != "exists") {
            throw new Error("not existential sentence");
        }
        this.addConstant(new Constant(
            label,
            "existential",
            reference
        ));
        var definingTrait = new Statement(
            existential.sentence.f.replacevars(existential.sentence.v, label),
            definingTraitLabel,
            reference
        );
        definingTrait.proof.type = "Extantiation";
        definingTrait.proof.arguments = reference;
        this.addStatement(definingTrait);
    }
    this.addFreeConstant = function (label) {
        this.addConstant(new Constant(label, "free"));
    }
    this.applyUniversalToConstant = function (reference, constantRef, label) {
        var universal = this.getLabeledStatement(reference);
        if (universal.sentence.type != "all") {
            throw new Error("not universal sentence");
        }
        if (this.getLabeledConstant(constantRef) == undefined) {
            throw new Error("constant not in context");
        }
        newStatement = new Statement(
            universal.sentence.f.replacevars(universal.sentence.v, constantRef),
            label
        );
        newStatement.proof.type = "universal"
        newStatement.proof.arguments = reference;
        this.addStatement(newStatement);
    }
}