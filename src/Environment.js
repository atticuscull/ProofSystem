function Constant(label, free=true) {
    this.label = label;
    this.free = free;
}

function Statement(sentence, label) {
    this.sentence = sentence;
    this.label = label;
    this.proof = {
        type: "",
        arguments: undefined,
    };
}

function Environment(parent=undefined, label=undefined) {
    this.label = parent? label: "main";
    this.parent = parent;
    this.statements = {};
    this.environments = {};
    this.constants = {};
    this.assumptions = [];
    this.addAssumption = function (sentence, label) {
        if (this.statements[label] != undefined) {
            throw new Error("labelAlreadyExists");
        }
        this.statements[label] = new Statement(sentence, label);
        this.statements[label].proof.type = "Asumption";
        this.assumptions.push(this.statements[label]);
        return this.statements[label];
    }
    this.createSubEnvironment = function(label) {
        if (this.statements[label] != undefined) {
            throw new Error("labelAlreadyExists");
        }
        newEnvironment = new Environment(this, label);
        this.environments[label] = newEnvironment;
    }
    this.borrow = function(reference) {
        if(reference.slice(0,2) == "<\\") {
            var statement = this.parent.borrow(reference.slice(2));
        } else {
            return this.statements[reference];
        }
        var borrowLabel = reference.split("<\\").join("<")
        var borrowedStatement = new Statement(
            statement.sentence,
            borrowLabel
        );
        borrowedStatement.proof.type = "borrowing";
        borrowedStatement.proof.arguments = reference;
        this.statements[borrowLabel] = borrowedStatement;
        return borrowedStatement;
    }
    this.getDependencies = function(reference) {
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
    this.getStatement = function(reference) {
        var path = reference.split("\\");
        var environmentReference = path.slice(0,-1).join("\\");
        var environment = this.getEnvironmentFromRef(environmentReference);
        var output = environment.statements[path.pop()];
        if (output == undefined) {
            throw new Error("invalid Statement reference");
        }
        return output;
    }
    this.getEnvironmentFromRef = function(reference) {
        var path = reference.split("\\");
        path.reverse();
        var thisEnvironment = this;
        while (path.length > 0) {
            nextEnvironmentLabel = path.pop();
            if (nextEnvironmentLabel == "<") {
                thisEnvironment = thisEnvironment.parent
            } else {
                thisEnvironment = thisEnvironment.environments[nextEnvironmentLabel];
                if (thisEnvironment == undefined) {
                    throw new Error("invalid Environment reference");
                }
            }
        }
        return thisEnvironment;
    }
    this.squash = function(reference, newLabel) {
        var dependencies = this.getDependencies(reference);
        var environment = this.getEnvironmentFromRef(reference.split("\\").slice(0,-1).join("\\"));
        var statement = this.getStatement(reference);
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

        freeVars = [];
        sentence.vars.forEach(variable => {
            constant = environment.constants[variable];
            if (constant.free) {
                freeVars.push(variable);
            } else {
                if (this.constants[variable] == undefined){
                    this.constants[variable] = new Constant(
                        variable,
                        false
                    );
                }
            }
        });

        while (freeVars.length > 0) {
            sentence = Formula.all(sentence, freeVars.pop());
        }

        var squashedStatement = new Statement(
            sentence,
            newLabel
        );
        squashedStatement.proof.type = "squash";
        squashedStatement.proof.arguments = reference;
        this.statements[newLabel] = squashedStatement;
    }
    this.and = function (label1, label2, newLabel = "") {
        if (newLabel == "") {
            newLabel += "and(" + label1 + "," + label2 + ")"
        }
        var sentence1 = this.statements[label1].sentence;
        var sentence2 = this.statements[label2].sentence;
        var newStatement = new Statement(
            Formula.and(sentence1, sentence2),
            newLabel
        );
        newStatement.proof.type = "and";
        newStatement.proof.arguments = [label1, label2];
        this.statements[newLabel] = newStatement;

    }
    this.getPath = function() {
        output = this.label;
        thisEnvironment = this;
        while (thisEnvironment.parent != undefined) {
            thisEnvironment = thisEnvironment.parent;
            output = thisEnvironment.label + "\\" + output;
        }
        return output;
    }
    this.matchAssumption = function(label, reference) {
        var parentStatement = this.getStatement(reference);
        var labeledStatement = this.statements[label];
        if(Formula.mathches(parentStatement.sentence, labeledStatement.sentence)) {
            labeledStatement.proof.type = "borrowing"
            labeledStatement.proof.arguments = reference;
        }
    }
    this.addConstantFromExistential = function (reference, label, definingTraitLabel) {
        existential = this.statements[reference];
        if (existential.sentence.type != "exists") {
            throw new Error("not existential sentence");
        }
        this.constants[label] = new Constant(label, false);
        var definingTrait = new Statement(
            existential.sentence.f.replacevars(existential.sentence.v, label),
            definingTraitLabel
        );
        definingTrait.proof.type = "Extantiation";
        definingTrait.proof.arguments = reference;
        this.statements[definingTraitLabel] = definingTrait;
    }
    this.addFreeConstant = function (label) {
        this.constants[label] = new Constant(label);
    }
    this.applyUniversalToConstant = function (reference, constantName, label) {
        universal = this.statements[reference];
        if (universal.sentence.type != "all") {
            throw new Error("not universal sentence");
        }
        if (this.constants[constantName] == undefined) {
            throw new Error("constant not in context");
        }
        newStatement = new Statement(
            universal.sentence.f.replacevars(universal.sentence.v, constantName),
            label
        );
        this.statements[label] = newStatement;

    }
}