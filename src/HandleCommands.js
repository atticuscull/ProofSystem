var commandLine = document.getElementById("commandLine");
var commandLog = document.getElementById("commandLog");

function EnvironmentHandler(environment) {
    this.environment = environment;
    var pathName = this.environment.getPath();

    this.collapser = document.createElement("button");
    this.collapser.setAttribute("id", pathName + "\\collapser");
    this.collapser.setAttribute("class", "collapser");
    this.collapser.setAttribute("type", "button");
    this.collapser.classList.toggle("active");
    this.collapser.innerHTML =  "v " + environment.label;

    this.wrapper = document.createElement("div");
    this.wrapper.setAttribute("id", pathName + "\\wrapper");
    this.wrapper.setAttribute("class", "wrapper");
    this.wrapper.style.display = "block";

    this.statementsHeader = document.createElement("h2");
    this.statementsHeader.setAttribute("id", pathName + "\\statementsHeader");
    this.statementsHeader.setAttribute("class", "statementsHeader");
    this.statementsHeader.innerHTML = "Statements";

    this.statements = document.createElement("p");
    this.statements.setAttribute("id", pathName + "\\statements");
    this.statements.setAttribute("class", "statements");

    this.constantsHeader = document.createElement("h2");
    this.constantsHeader.setAttribute("id", pathName + "\\constantsHeader");
    this.constantsHeader.setAttribute("class", "constantsHeader");
    this.constantsHeader.innerHTML = "Constants";

    this.constants = document.createElement("p");
    this.constants.setAttribute("id", pathName + "\\constants");
    this.constants.setAttribute("class", "constants");

    parentDiv = (environment.parent == undefined) ? document.getElementById("leftSide") : this.environment.parent.handler.wrapper
    parentDiv.appendChild(this.collapser);
    parentDiv.appendChild(this.wrapper);
    this.wrapper.appendChild(this.statementsHeader);
    this.wrapper.appendChild(this.statements);
    this.wrapper.appendChild(this.constantsHeader);
    this.wrapper.appendChild(this.constants);

    this.unhideStatements = function() {
        this.statementsHeader.style.display = "block";
    }

    this.unhideConstants = function () {
        this.constantsHeader.style.display = "block";
    }

    this.isOpen = true;
    this.isCurrent = false;

    this.setOpen = function() {
        this.isOpen = true;
        this.wrapper.style.display = "block";
        this.collapser.innerHTML = "v " + this.environment.label
        this.environment.parent?.handler?.setOpen();
    }

    this.setClosed = function () {
        this.isOpen = false;
        this.wrapper.style.display = "none";
        this.collapser.innerHTML = "> " + this.environment.label
    }

    this.setNotCurrent = function () {
        this.isCurrent = false;
        this.collapser.classList.remove("current");
    }

    this.setCurrent = function () {
        this.isCurrent = true;
        this.collapser.classList.add("current");
    }

    this.collapser.addEventListener("click", function () {
        var content = this.nextElementSibling;
        if (content.style.display === "block") {
            content.style.display = "none";
            this.innerHTML = "> " + environment.label
        } else {
            content.style.display = "block";
            this.innerHTML = "v " + environment.label
        }
    });

    this.refreshStatements = function() {
        var lines = Object.values(this.environment.statements).map(statement => {
            var output = statement.label + ": " + formulaToString(statement.sentence);
            return cleanForHTML(output);
        });
        if (lines.length > 0) {
            this.unhideStatements();
            this.statements.innerHTML = lines.join("<br>");
        }
    }

    this.refreshConstants = function() {
        var lines = Object.values(this.environment.constants).map(constant => {
            var output = constant.label;
            return cleanForHTML(output);
        });
        if (lines.length > 0) {
            this.unhideConstants();
            this.constants.innerHTML = lines.join("<br>");
        }
    }

    this.refreshBoth = function() {
        this.refreshStatements();
        this.refreshConstants();
    }

    this.refreshPath = function(reference) {
        var environmentsToRefresh = [this.environment];
        var thisEnviroment = this.environment;
        var path = reference.split("\\")
        path.reverse();
        while (path.length > 0) {
            nextEnvironmentLabel = path.pop();
            if (nextEnvironmentLabel == "<") {
                thisEnviroment = thisEnviroment.parent;
            } else {
                thisEnviroment = thisEnviroment.environments[nextEnvironmentLabel];
            }
            if (thisEnviroment == undefined) {
                throw new Error("invalid Environment reference");
            }
            environmentsToRefresh.push(thisEnviroment);
        }
        environmentsToRefresh.forEach(env => {
            env.handler.refreshBoth();
        });
    }

}

function setNewCurrent(environment) {
    currentEnvironment.handler.setNotCurrent();
    currentEnvironment = environment;
    currentEnvironment.handler.setCurrent();
}

var MainEnvironment = new Environment();
MainEnvironment.handler = new EnvironmentHandler(MainEnvironment);
var currentEnvironment = MainEnvironment;

MainEnvironment.handler.wrapper.style["margin-left"] = "0px";
MainEnvironment.handler.collapser.style["margin-left"] = "0px";
MainEnvironment.handler.setCurrent();


REPLACEMENTS = {
    "\\E": "\u2203",
    "\\A": "\u2200",
    "\\in": "\u2208",
    "\\n": "\u00ac",
    "\\and": "\u2227",
    "\\or": "\u2228",
    "\\imp": "\u2192",
}

function formulaReplacements(string) {
    output = string;
    Object.keys(REPLACEMENTS).forEach(key => {
        output = output.split(key).join(REPLACEMENTS[key]);
    });
    return output;
}


function enterCommand(command) {
    var commandName = command.split(" ")[0];
    var argument = command.split(" ").slice(1).join(" ");
    switch (commandName) {
        case "assume":
            if (!argument.includes(" as ")){
                throw new Error("assume requires a follow up \"as\"");
            }
            var [sentence, label] = argument.split(" as ");

            var cleanedSentence = formulaReplacements(sentence);
            if (!matchParens(cleanedSentence)) {
                throw new Error("parenthises don't match");
            }
            statement = currentEnvironment.addAssumption(interpretSentence(cleanedSentence), label);
            currentEnvironment.handler.refreshStatements();
            break;
        case "create":
            argument = argument.split(" ").join("");
            currentEnvironment.createSubEnvironment(argument);
            newEnvironment = currentEnvironment.environments[argument];
            newEnvironment.handler = new EnvironmentHandler(newEnvironment);
            setNewCurrent(newEnvironment);
            break;
        case "move":
            argument = argument.split(" ").join("");
            setNewCurrent(currentEnvironment.getEnvironmentFromRef(argument));
            break;
        case "preset":
            argument = argument.split(" ").join("");
            enterCommand(presets[argument]);
            return true;
        case "instantiate":
            var [label, argument] = argument.split(" from ");
            var [reference, traitLabel] = argument.split (" with ");
            label = label.split(" ").join("");
            reference = reference.split(" ").join("");
            traitLabel = traitLabel.split(" ").join("");
            currentEnvironment.addConstantFromExistential(reference, label, traitLabel);
            currentEnvironment.handler.refreshBoth();
            break;
        case "const":
            argument = argument.split(" ").join("");
            currentEnvironment.addFreeConstant(argument);
            currentEnvironment.handler.refreshConstants();
            break;
        case "squash":
            var [reference, label] = argument.split(" as ");
            label = label.split(" ").join("");
            reference = reference.split(" ").join("");
            currentEnvironment.squash(reference, label);
            currentEnvironment.handler.refreshBoth();
            break;
        case "apply":
            var [reference, argument] = argument.split(" to ");
            var [constantName, label] = argument.split(" with ");
            label = label.split(" ").join("");
            reference = reference.split(" ").join("");
            constantName = constantName.split(" ").join("");
            currentEnvironment.applyUniversalToConstant(reference, constantName, label);
            currentEnvironment.handler.refreshBoth();
            break;
        case "contra":
            var [reference, label] = argument.split(" as ");
            label = label.split(" ").join("");
            reference = reference.split(" ").join("");
            currentEnvironment.contrapositive(reference, label);
            currentEnvironment.handler.refreshStatements();
            break;
        case "impT":
            var [reference, argument] = argument.split(" implies ");
            var [sentence, label] = argument.split(" as ");
            label = label.split(" ").join("");
            reference = reference.split(" ").join("");
            var cleanedSentence = formulaReplacements(sentence);
            if (!matchParens(cleanedSentence)) {
                throw new Error("parenthises don't match");
            }
            currentEnvironment.impliesTrue(reference, interpretSentence(cleanedSentence), label);
            currentEnvironment.handler.refreshStatements();
            break;
        case "and":
            var [argument, label] = argument.split(" as ");
            var [ref1, ref2] = argument.split(" ");
            currentEnvironment.and(ref1, ref2, label);
            currentEnvironment.handler.refreshStatements();
            break;
        case "modusP":
            var [argument, label] = argument.split(" as ");
            var [ref1, ref2] = argument.split(" ");
            currentEnvironment.modusPonens(ref1, ref2, label);
            currentEnvironment.handler.refreshStatements();
            break;
        default:
            return false;        
    }
    currentEnvironment.handler.setOpen();
    commandLog.innerHTML += cleanForHTML(command) + ";<br>";
    return true;
}

function cleanForHTML(string) {
    return string.split("<").join("&lt;").split(">").join("&gt;")
}

commandLine.addEventListener("keypress", function(event) {
    if (event.key == "Enter") {
        event.preventDefault();
        if (commandLine.value != ""){
            var commands = commandLine.value.split("\n").join("").split(";");
            commands.reverse();
            while (commands.length > 0) {
                var command = commands.pop();
                var success = enterCommand(command);
                if (!success) {
                    commands.push(command);
                    commands.reverse();
                    break;
                }
            }
            commandLine.value = commands.join(";");
            
        }
    }
});


var presets = {
    ADDEXTENSIONALITY: "assume (\\A x)((\\A y)( ((\\A z)( ((z \\in x) \\imp (z \\in y)) \\and ((z \\in y) \\imp (z \\in x)) )) \\imp (x=y) )) as ext",
    ADDUNION: "assume (\\A X)((\\E U)( (\\A z) (((z \\in U) \\imp ((\\E x) ((x \\in X) \\and (z \\in x)))) \\and (((\\E x) ((x \\in X) \\and (z \\in x))) \\imp (z \\in U))) )) as union",
    EXISTSELEMENT: "assume (\\E x)(x=x)",
    EMPTYSET: "assume (\\E x)((\\A y)(\\n (y\\in x))) as emptyset"
}
