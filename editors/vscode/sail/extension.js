const path = require("path");
const vscode = require("vscode");
const { LanguageClient } = require("vscode-languageclient/node");

let client;
let clientReady = Promise.resolve();
let documentationChannel;

const taskSource = "Sail";
const taskType = "sail";

function extensionConfig() {
  return vscode.workspace.getConfiguration("sail");
}

function hasConfiguredValue(config, key) {
  const inspection = config.inspect(key);
  if (!inspection) {
    return false;
  }
  return [
    inspection.globalValue,
    inspection.workspaceValue,
    inspection.workspaceFolderValue,
    inspection.globalLanguageValue,
    inspection.workspaceLanguageValue,
    inspection.workspaceFolderLanguageValue,
  ].some((value) => value !== undefined);
}

function nonEmptyString(value) {
  return typeof value === "string" && value.trim().length > 0;
}

function resolveWorkspacePath(value) {
  if (!nonEmptyString(value)) {
    return value;
  }

  if (path.isAbsolute(value) || (!value.includes("/") && !value.includes("\\"))) {
    return value;
  }

  const folder = vscode.workspace.workspaceFolders && vscode.workspace.workspaceFolders[0];
  return folder ? path.join(folder.uri.fsPath, value) : value;
}

function initializationOptions() {
  const config = extensionConfig();
  const options = {};
  const cOutput = config.get("cOutput");
  const cMap = config.get("cMap");
  const docinfo = config.get("docinfo");
  const artifactIndex = config.get("artifactIndex");
  const sailExecutable = config.get("executablePath");
  const projectFile = config.get("projectFile");
  const projectModules = config.get("projectModules") || [];
  const projectAllModules = config.get("projectAllModules");
  const diagnosticsEnabled = config.get("diagnostics.enable");

  if (nonEmptyString(cOutput)) {
    options.cOutput = cOutput;
  }
  if (nonEmptyString(cMap)) {
    options.cMap = cMap;
  }
  if (nonEmptyString(docinfo)) {
    options.docinfo = docinfo;
  }
  if (nonEmptyString(artifactIndex)) {
    options.artifactIndex = artifactIndex;
  }
  if (nonEmptyString(sailExecutable)) {
    options.sailExecutable = resolveWorkspacePath(sailExecutable);
  }
  if (nonEmptyString(projectFile)) {
    options.projectFile = projectFile;
  }
  if (Array.isArray(projectModules)) {
    const modules = projectModules.filter(nonEmptyString);
    if (modules.length > 0) {
      options.projectModules = modules;
    }
  }
  if (
    typeof projectAllModules === "boolean" &&
    (hasConfiguredValue(config, "projectAllModules") || nonEmptyString(projectFile) || options.projectModules)
  ) {
    options.allModules = projectAllModules;
  }
  if (typeof diagnosticsEnabled === "boolean") {
    options.diagnostics = diagnosticsEnabled;
  }

  return options;
}

function positionParams(editor) {
  return {
    textDocument: { uri: editor.document.uri.toString() },
    position: {
      line: editor.selection.active.line,
      character: editor.selection.active.character,
    },
  };
}

function activeSailEditor() {
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== "sail") {
    vscode.window.showWarningMessage("Open a Sail file first.");
    return undefined;
  }
  return editor;
}

async function ensureClient() {
  if (!client) {
    throw new Error("Sail language server is not running.");
  }
  await clientReady;
  return client;
}

async function requestAtCursor(method) {
  const editor = activeSailEditor();
  if (!editor) {
    return undefined;
  }
  return (await ensureClient()).sendRequest(method, positionParams(editor));
}

function toRange(range) {
  return new vscode.Range(
    new vscode.Position(range.start.line, range.start.character),
    new vscode.Position(range.end.line, range.end.character)
  );
}

async function revealLocation(location) {
  if (!location || !location.uri || !location.range) {
    return false;
  }

  const document = await vscode.workspace.openTextDocument(vscode.Uri.parse(location.uri));
  await vscode.window.showTextDocument(document, {
    selection: toRange(location.range),
    preview: false,
  });
  return true;
}

async function goToGeneratedC() {
  const location = await requestAtCursor("sail/generatedC");
  if (!(await revealLocation(location))) {
    vscode.window.showWarningMessage("No generated C location found for the current Sail identifier.");
  }
}

async function showCName() {
  const result = await requestAtCursor("sail/cName");
  if (!result || !result.cName) {
    vscode.window.showWarningMessage("No generated C name found for the current Sail identifier.");
    return;
  }

  const sailName = result.sailName ? `${result.sailName} -> ` : "";
  const source = result.source ? ` (${result.source})` : "";
  const fallback = result.fallbackReason ? ` ${result.fallbackReason}` : "";
  vscode.window.showInformationMessage(`${sailName}${result.cName}${source}${fallback}`);
}

async function showDocumentation() {
  const result = await requestAtCursor("sail/documentation");
  if (!result || !result.markdown) {
    vscode.window.showWarningMessage("No Sail documentation found for the current identifier.");
    return;
  }

  if (!documentationChannel) {
    documentationChannel = vscode.window.createOutputChannel("Sail Documentation");
  }
  documentationChannel.clear();
  documentationChannel.appendLine(result.markdown);
  documentationChannel.show(true);
}

async function showType() {
  const result = await requestAtCursor("sail/type");
  if (!result) {
    vscode.window.showWarningMessage("No Sail type information found for the current identifier.");
    return;
  }

  const typeText = result.type || "No type metadata found.";
  vscode.window.showInformationMessage(`${result.name}: ${typeText}`);
}

function quoteShell(value) {
  if (process.platform === "win32") {
    return `"${value.replace(/"/g, '\\"')}"`;
  }
  return `'${value.replace(/'/g, "'\\''")}'`;
}

function compilerCheckArgs(document) {
  const config = extensionConfig();
  const projectFile = config.get("projectFile");
  const projectModules = config.get("projectModules") || [];

  if (!nonEmptyString(projectFile)) {
    return [document.uri.fsPath];
  }

  const args = ["-project", resolveWorkspacePath(projectFile)];
  if (Array.isArray(projectModules) && projectModules.some(nonEmptyString)) {
    args.push(...projectModules.filter(nonEmptyString));
  } else if (config.get("projectAllModules") !== false) {
    args.push("-all_modules");
  }
  return args;
}

function checkCurrentFile() {
  const editor = activeSailEditor();
  if (!editor || editor.document.isUntitled) {
    return;
  }

  const config = extensionConfig();
  const sail = resolveWorkspacePath(config.get("executablePath") || "sail");
  const args = ["-no_color", "-just_check", ...compilerCheckArgs(editor.document)];
  const terminal = vscode.window.createTerminal("Sail Check");
  terminal.show(true);
  terminal.sendText([sail, ...args].map(quoteShell).join(" "));
}

function taskWorkspaceScope() {
  return (vscode.workspace.workspaceFolders && vscode.workspace.workspaceFolders[0]) || vscode.TaskScope.Workspace;
}

function taskShellOptions() {
  const folder = workspaceFolderPath();
  return folder ? { cwd: folder } : undefined;
}

function sailShellCommand(args) {
  const config = extensionConfig();
  const sail = resolveWorkspacePath(config.get("executablePath") || "sail");
  return [sail, ...args].map(quoteShell).join(" ");
}

function resolveTaskFilePath(file) {
  if (!nonEmptyString(file)) {
    return undefined;
  }

  if (path.isAbsolute(file)) {
    return file;
  }

  const folder = workspaceFolderPath();
  return folder ? path.join(folder, file) : file;
}

function projectCheckArgsFromDefinition(definition) {
  const config = extensionConfig();
  const projectFile = definition.projectFile || config.get("projectFile");
  if (!nonEmptyString(projectFile)) {
    return undefined;
  }

  const args = ["-no_color", "-just_check", "-project", resolveWorkspacePath(projectFile)];
  const modules = Array.isArray(definition.projectModules) ? definition.projectModules : config.get("projectModules") || [];
  if (Array.isArray(modules) && modules.some(nonEmptyString)) {
    args.push(...modules.filter(nonEmptyString));
  } else if (definition.projectAllModules !== false && config.get("projectAllModules") !== false) {
    args.push("-all_modules");
  }
  return args;
}

function makeSailTask(definition, name, args, group) {
  const task = new vscode.Task(
    definition,
    taskWorkspaceScope(),
    name,
    taskSource,
    new vscode.ShellExecution(sailShellCommand(args), taskShellOptions())
  );
  task.group = group;
  task.problemMatchers = [];
  task.presentationOptions = {
    reveal: vscode.TaskRevealKind.Always,
    panel: vscode.TaskPanelKind.Dedicated,
  };
  return task;
}

function taskFromDefinition(definition) {
  switch (definition.task) {
    case "checkFile": {
      const file = resolveTaskFilePath(definition.file);
      if (!file) {
        return undefined;
      }
      return makeSailTask(definition, `Check ${path.basename(file)}`, ["-no_color", "-just_check", file], vscode.TaskGroup.Test);
    }
    case "checkProject": {
      const args = projectCheckArgsFromDefinition(definition);
      if (!args) {
        return undefined;
      }
      return makeSailTask(definition, "Check Project", args, vscode.TaskGroup.Test);
    }
    case "generateC": {
      const file = resolveTaskFilePath(definition.file);
      if (!file) {
        return undefined;
      }
      const args = ["-c"];
      if (definition.emitLspMap !== false) {
        args.push("--c-emit-lsp-map");
      }
      args.push(file);
      return makeSailTask(definition, `Generate C for ${path.basename(file)}`, args, vscode.TaskGroup.Build);
    }
    default:
      return undefined;
  }
}

function currentSailDocument() {
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== "sail" || editor.document.isUntitled) {
    return undefined;
  }
  return editor.document;
}

function provideSailTasks() {
  const tasks = [];
  const document = currentSailDocument();
  if (document) {
    const file = workspaceRelativePath(document.uri);
    tasks.push(
      taskFromDefinition({ type: taskType, task: "checkFile", file }),
      taskFromDefinition({ type: taskType, task: "generateC", file, emitLspMap: true })
    );
  }

  const config = extensionConfig();
  const projectFile = config.get("projectFile");
  if (nonEmptyString(projectFile)) {
    tasks.push(
      taskFromDefinition({
        type: taskType,
        task: "checkProject",
        projectFile,
        projectModules: config.get("projectModules") || [],
        projectAllModules: config.get("projectAllModules") !== false,
      })
    );
  }

  return tasks.filter(Boolean);
}

function registerTaskProvider(context) {
  context.subscriptions.push(
    vscode.tasks.registerTaskProvider(taskType, {
      provideTasks: provideSailTasks,
      resolveTask(task) {
        return taskFromDefinition(task.definition);
      },
    })
  );
}

async function formatCurrentFile() {
  const editor = activeSailEditor();
  if (!editor) {
    return;
  }
  await vscode.commands.executeCommand("editor.action.formatDocument");
}

function workspaceFolderPath() {
  const folder = vscode.workspace.workspaceFolders && vscode.workspace.workspaceFolders[0];
  return folder && folder.uri.fsPath;
}

function workspaceRelativePath(uri) {
  const folder = workspaceFolderPath();
  if (!folder) {
    return uri.fsPath;
  }
  return path.relative(folder, uri.fsPath) || path.basename(uri.fsPath);
}

async function chooseProjectFile() {
  const files = await vscode.workspace.findFiles(
    "**/*.sail_project",
    "{**/_build/**,**/.git/**,**/.worktrees/**,**/node_modules/**}",
    100
  );
  if (files.length === 0) {
    vscode.window.showWarningMessage("No .sail_project files found in this workspace.");
    return;
  }

  const items = [
    { label: "Use current file only", description: "Clear sail.projectFile", uri: undefined },
    ...files.map((uri) => ({
      label: workspaceRelativePath(uri),
      description: uri.fsPath,
      uri,
    })),
  ];
  const picked = await vscode.window.showQuickPick(items, {
    placeHolder: "Select the Sail project file used for diagnostics and checks",
  });
  if (!picked) {
    return;
  }

  const value = picked.uri ? workspaceRelativePath(picked.uri) : "";
  await extensionConfig().update("projectFile", value, vscode.ConfigurationTarget.Workspace);
  vscode.window.showInformationMessage(value ? `Sail project file set to ${value}.` : "Sail project file cleared.");
}

async function setProjectModules() {
  const config = extensionConfig();
  const current = config.get("projectModules") || [];
  const value = await vscode.window.showInputBox({
    prompt: "Project module names, separated by commas or spaces. Leave empty to use all modules.",
    value: Array.isArray(current) ? current.join(", ") : "",
  });
  if (value === undefined) {
    return;
  }

  const modules = value
    .split(/[,\s]+/)
    .map((module) => module.trim())
    .filter(nonEmptyString);
  await config.update("projectModules", modules, vscode.ConfigurationTarget.Workspace);
  vscode.window.showInformationMessage(
    modules.length > 0 ? `Sail project modules set to ${modules.join(", ")}.` : "Sail project modules cleared."
  );
}

async function startClient(context) {
  if (client) {
    await client.stop();
    client = undefined;
  }

  const config = extensionConfig();
  const command = resolveWorkspacePath(config.get("lsp.path") || "sail_lsp");
  const args = config.get("lsp.args") || ["--stdio"];
  const folder = vscode.workspace.workspaceFolders && vscode.workspace.workspaceFolders[0];
  const serverOptions = { command, args, options: folder ? { cwd: folder.uri.fsPath } : undefined };
  const clientOptions = {
    documentSelector: [{ scheme: "file", language: "sail" }],
    initializationOptions: initializationOptions(),
    synchronize: {
      configurationSection: "sail",
      fileEvents: [
        vscode.workspace.createFileSystemWatcher("**/*.{sail,sail_project,c,cpp}"),
        vscode.workspace.createFileSystemWatcher("**/{sail.lsp.json,.sail_lsp.json,out.sail_lsp.json,out.sail_artifacts.json}"),
        vscode.workspace.createFileSystemWatcher("**/*.symbols.json"),
        vscode.workspace.createFileSystemWatcher("**/{doc.json,docinfo.json,*.docinfo.json}"),
      ],
    },
  };

  client = new LanguageClient("sailLsp", "Sail Language Server", serverOptions, clientOptions);
  clientReady = client.start().catch((error) => {
    vscode.window.showWarningMessage(`Failed to start sail_lsp: ${error.message}`);
    throw error;
  });
  context.subscriptions.push({ dispose: () => client && client.stop() });
}

async function restartLanguageServer(context) {
  await startClient(context);
  vscode.window.showInformationMessage("Sail language server restarted.");
}

function activate(context) {
  registerTaskProvider(context);

  context.subscriptions.push(
    vscode.commands.registerCommand("sail.goToGeneratedC", goToGeneratedC),
    vscode.commands.registerCommand("sail.showCName", showCName),
    vscode.commands.registerCommand("sail.showType", showType),
    vscode.commands.registerCommand("sail.showDocumentation", showDocumentation),
    vscode.commands.registerCommand("sail.checkCurrentFile", checkCurrentFile),
    vscode.commands.registerCommand("sail.formatCurrentFile", formatCurrentFile),
    vscode.commands.registerCommand("sail.chooseProjectFile", chooseProjectFile),
    vscode.commands.registerCommand("sail.setProjectModules", setProjectModules),
    vscode.commands.registerCommand("sail.restartLanguageServer", () => restartLanguageServer(context)),
    vscode.workspace.onDidChangeConfiguration((event) => {
      if (event.affectsConfiguration("sail")) {
        restartLanguageServer(context);
      }
    })
  );

  startClient(context);
}

async function deactivate() {
  if (client) {
    await client.stop();
    client = undefined;
  }
}

module.exports = {
  activate,
  deactivate,
};
