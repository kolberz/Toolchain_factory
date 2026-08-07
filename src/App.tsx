import React, { useState, useMemo } from 'react';
import {
  Cpu, Zap, Shield, Flame, Atom, Code, Sparkles, Server, Activity, Box,
  Terminal, Palette, Layout, FileCode, CheckCircle2, Globe, Award, Eye,
  Minus, ShieldCheck, Container, GitBranch, Gitlab, Circle, Cloud, Triangle,
  Layers, Github, Download, Copy, Check, Play, AlertTriangle, RefreshCw,
  FileText, FolderGit2, Package, Search, ChevronRight, Info, HelpCircle, Send,
  Wrench, Bug
} from 'lucide-react';

import {
  ToolchainConfig, GeneratedFile, SmallZipUnit, ZipDependencyClassification,
  CompatibilityIssue, PipelineStep
} from './types/toolchain';
import { TOOLCHAIN_PRESETS, ToolchainPreset } from './data/presets';
import {
  FRAMEWORK_OPTIONS, RUNTIME_OPTIONS, BUNDLER_OPTIONS, STYLING_OPTIONS,
  TESTING_OPTIONS, LINTER_OPTIONS, CONTAINER_OPTIONS, CICD_OPTIONS, DEPLOYMENT_OPTIONS
} from './data/options';
import { validateToolchainConfig } from './utils/compatibilityChecker';
import { generateToolchainFiles, generateSmallZipUnits } from './utils/toolchainGenerator';
import { downloadProjectZip } from './utils/zipExporter';

export default function App() {
  // Navigation State
  const [activeTab, setActiveTab] = useState<'architect' | 'smallzips' | 'files' | 'pipeline' | 'ai'>('architect');
  
  // Selected Toolchain Configuration State
  const [config, setConfig] = useState<ToolchainConfig>(TOOLCHAIN_PRESETS[0].config);
  const [selectedPresetId, setSelectedPresetId] = useState<string>(TOOLCHAIN_PRESETS[0].id);

  // File Viewer State
  const [selectedFilePath, setSelectedFilePath] = useState<string>('README.md');
  const [copiedFilePath, setCopiedFilePath] = useState<string | null>(null);
  const [copiedCommand, setCopiedCommand] = useState<string | null>(null);

  // Diagnostic Capsule Custom State
  const [diagnosticCode, setDiagnosticCode] = useState<string>(
    `import Mathlib.Data.Nat.Basic\n\ntheorem nat_add_comm_buggy (n m : ℕ) : n + m = m + n := by\n  rfl -- Expected error: type mismatch`
  );
  const [diagnosticErrorLog, setDiagnosticErrorLog] = useState<string>(
    `failing/FileA.lean:4:2: error: type mismatch\n  rfl\nhas type\n  n + m = n + m\nbut is expected to have type\n  n + m = m + n`
  );

  // AI Assistant Chat State
  const [aiPrompt, setAiPrompt] = useState<string>('');
  const [aiLoading, setAiLoading] = useState<boolean>(false);
  const [aiMessages, setAiMessages] = useState<Array<{ sender: 'user' | 'assistant'; text: string }>>([
    {
      sender: 'assistant',
      text: 'Hello! I am your AI Toolchain Architect. Ask me anything about configuring modern web stacks, Docker containers, CI/CD matrices, or setting up Lean 4 + Mathlib formal verification small ZIP strategies.'
    }
  ]);

  // Pipeline Simulator State
  const [pipelineSteps, setPipelineSteps] = useState<PipelineStep[]>([
    { id: '1', name: 'Lint & Static Analysis', category: 'lint', command: 'npm run lint', estimatedTimeSec: 2, status: 'idle', logOutput: [] },
    { id: '2', name: 'Execute Test Suite', category: 'test', command: 'npm run test', estimatedTimeSec: 4, status: 'idle', logOutput: [] },
    { id: '3', name: 'Compile Production Build', category: 'build', command: 'npm run build', estimatedTimeSec: 6, status: 'idle', logOutput: [] },
    { id: '4', name: 'Build Multi-Stage Docker Image', category: 'container', command: 'docker build -t app:latest .', estimatedTimeSec: 8, status: 'idle', logOutput: [] },
    { id: '5', name: 'Deploy to Cloud Run', category: 'deploy', command: 'gcloud run deploy', estimatedTimeSec: 5, status: 'idle', logOutput: [] }
  ]);
  const [isRunningPipeline, setIsRunningPipeline] = useState<boolean>(false);

  // Computed Values
  const compatibilityIssues: CompatibilityIssue[] = useMemo(() => {
    return validateToolchainConfig(config);
  }, [config]);

  const generatedFiles: GeneratedFile[] = useMemo(() => {
    return generateToolchainFiles(config);
  }, [config]);

  const smallZipUnits: SmallZipUnit[] = useMemo(() => {
    return generateSmallZipUnits(config);
  }, [config]);

  const selectedFile = useMemo(() => {
    return generatedFiles.find(f => f.path === selectedFilePath) || generatedFiles[0];
  }, [generatedFiles, selectedFilePath]);

  // Preset Selector Handler
  const handleSelectPreset = (preset: ToolchainPreset) => {
    setSelectedPresetId(preset.id);
    setConfig(preset.config);
  };

  // Download All Project Zip
  const handleDownloadFullZip = async () => {
    await downloadProjectZip(config.projectName, generatedFiles);
  };

  // Download Single Small Zip
  const handleDownloadSmallZip = async (unit: SmallZipUnit) => {
    await downloadProjectZip(`${config.projectName}-${unit.id}`, unit.files);
  };

  // Copy helper
  const copyToClipboard = (text: string, label: string) => {
    navigator.clipboard.writeText(text);
    setCopiedCommand(label);
    setTimeout(() => setCopiedCommand(null), 2500);
  };

  // Pipeline Runner Simulation
  const handleRunPipelineSim = async () => {
    setIsRunningPipeline(true);
    const updatedSteps = pipelineSteps.map(s => ({ ...s, status: 'idle' as const, logOutput: [] }));
    setPipelineSteps(updatedSteps);

    for (let i = 0; i < updatedSteps.length; i++) {
      updatedSteps[i].status = 'running';
      setPipelineSteps([...updatedSteps]);
      await new Promise(r => setTimeout(r, 1200));

      updatedSteps[i].status = 'success';
      updatedSteps[i].logOutput = [
        `> ${updatedSteps[i].command}`,
        `[INFO] Starting ${updatedSteps[i].name}...`,
        `[SUCCESS] Step finished in ${updatedSteps[i].estimatedTimeSec}s.`
      ];
      setPipelineSteps([...updatedSteps]);
    }
    setIsRunningPipeline(false);
  };

  // AI Chat Request handler
  const handleSendAiPrompt = async () => {
    if (!aiPrompt.trim()) return;
    const userMsg = aiPrompt.trim();
    setAiPrompt('');
    setAiMessages(prev => [...prev, { sender: 'user', text: userMsg }]);
    setAiLoading(true);

    try {
      const systemInstruction = `You are an expert DevOps Engineer and Formal Verification Architect specializing in modern TypeScript toolchains and Lean 4 + Mathlib small ZIP strategies.
Current Config: ${JSON.stringify(config)}
Answer the user concisely and suggest actionable configuration changes or code tactics.`;

      const res = await fetch('/api/genai', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ prompt: userMsg, systemInstruction })
      });
      const data = await res.json();
      if (data.text) {
        setAiMessages(prev => [...prev, { sender: 'assistant', text: data.text }]);
      } else {
        setAiMessages(prev => [...prev, { sender: 'assistant', text: data.error || 'Failed to get response from AI.' }]);
      }
    } catch (err: any) {
      setAiMessages(prev => [...prev, { sender: 'assistant', text: 'Error connecting to AI service: ' + err.message }]);
    } finally {
      setAiLoading(false);
    }
  };

  // Render Classification Badge
  const renderClassificationBadge = (classification: ZipDependencyClassification) => {
    switch (classification) {
      case 'SELF-CONTAINED':
        return <span className="px-2.5 py-0.5 rounded-full text-xs font-mono font-semibold bg-emerald-500/10 text-emerald-400 border border-emerald-500/20">SELF-CONTAINED</span>;
      case 'TOOLCHAIN-DEPENDENT':
        return <span className="px-2.5 py-0.5 rounded-full text-xs font-mono font-semibold bg-blue-500/10 text-blue-400 border border-blue-500/20">TOOLCHAIN-DEPENDENT</span>;
      case 'MATHLIB-DEPENDENT':
        return <span className="px-2.5 py-0.5 rounded-full text-xs font-mono font-semibold bg-indigo-500/10 text-indigo-400 border border-indigo-500/20">MATHLIB-DEPENDENT</span>;
      case 'SOURCE PATCH':
        return <span className="px-2.5 py-0.5 rounded-full text-xs font-mono font-semibold bg-purple-500/10 text-purple-400 border border-purple-500/20">SOURCE PATCH</span>;
      case 'DIAGNOSTIC':
        return <span className="px-2.5 py-0.5 rounded-full text-xs font-mono font-semibold bg-amber-500/10 text-amber-400 border border-amber-500/20">DIAGNOSTIC</span>;
    }
  };

  return (
    <div className="min-h-screen bg-slate-950 text-slate-100 font-sans selection:bg-indigo-500 selection:text-white">
      {/* Top Banner & Header */}
      <header className="border-b border-slate-800 bg-slate-900/80 sticky top-0 z-50 backdrop-blur-md">
        <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 h-16 flex items-center justify-between">
          <div className="flex items-center space-x-3">
            <div className="p-2 bg-gradient-to-tr from-indigo-600 to-violet-600 rounded-xl text-white shadow-lg shadow-indigo-500/20">
              <Cpu className="w-5 h-5" />
            </div>
            <div>
              <div className="flex items-center gap-2">
                <span className="font-bold text-lg text-white tracking-tight">Toolchain Factory</span>
                <span className="text-[10px] uppercase font-mono px-2 py-0.5 bg-indigo-500/20 text-indigo-300 rounded-full border border-indigo-500/30">
                  v2.5
                </span>
              </div>
              <p className="text-xs text-slate-400 hidden sm:block">Modern Developer Toolchain & Lean 4 Diagnostic Architect</p>
            </div>
          </div>

          {/* Tab Navigation */}
          <nav className="flex items-center space-x-1 sm:space-x-2 bg-slate-950 p-1 rounded-xl border border-slate-800">
            <button
              onClick={() => setActiveTab('architect')}
              className={`px-3 py-1.5 rounded-lg text-xs font-medium transition-all flex items-center gap-1.5 ${
                activeTab === 'architect' ? 'bg-indigo-600 text-white shadow-sm' : 'text-slate-400 hover:text-slate-200'
              }`}
            >
              <Wrench className="w-3.5 h-3.5" />
              <span>Architect</span>
            </button>

            <button
              onClick={() => setActiveTab('smallzips')}
              className={`px-3 py-1.5 rounded-lg text-xs font-medium transition-all flex items-center gap-1.5 ${
                activeTab === 'smallzips' ? 'bg-indigo-600 text-white shadow-sm' : 'text-slate-400 hover:text-slate-200'
              }`}
            >
              <Package className="w-3.5 h-3.5 text-amber-400" />
              <span>Small ZIP Strategy</span>
            </button>

            <button
              onClick={() => setActiveTab('files')}
              className={`px-3 py-1.5 rounded-lg text-xs font-medium transition-all flex items-center gap-1.5 ${
                activeTab === 'files' ? 'bg-indigo-600 text-white shadow-sm' : 'text-slate-400 hover:text-slate-200'
              }`}
            >
              <FileCode className="w-3.5 h-3.5" />
              <span>Generated Code ({generatedFiles.length})</span>
            </button>

            <button
              onClick={() => setActiveTab('pipeline')}
              className={`px-3 py-1.5 rounded-lg text-xs font-medium transition-all flex items-center gap-1.5 ${
                activeTab === 'pipeline' ? 'bg-indigo-600 text-white shadow-sm' : 'text-slate-400 hover:text-slate-200'
              }`}
            >
              <Terminal className="w-3.5 h-3.5" />
              <span>CI/CD Pipeline</span>
            </button>

            <button
              onClick={() => setActiveTab('ai')}
              className={`px-3 py-1.5 rounded-lg text-xs font-medium transition-all flex items-center gap-1.5 ${
                activeTab === 'ai' ? 'bg-indigo-600 text-white shadow-sm' : 'text-slate-400 hover:text-slate-200'
              }`}
            >
              <Sparkles className="w-3.5 h-3.5 text-indigo-300" />
              <span>AI Architect</span>
            </button>
          </nav>

          {/* Download Action */}
          <button
            onClick={handleDownloadFullZip}
            className="px-3.5 py-2 bg-gradient-to-r from-emerald-600 to-teal-600 hover:from-emerald-500 hover:to-teal-500 text-white text-xs font-semibold rounded-xl shadow-lg shadow-emerald-600/20 flex items-center gap-1.5 transition-all"
          >
            <Download className="w-4 h-4" />
            <span className="hidden md:inline">Export Full ZIP</span>
          </button>
        </div>
      </header>

      {/* Main Content Area */}
      <main className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 py-6">

        {/* Git Remote Strip (First Commit Quick Commands) */}
        <section className="mb-6 bg-slate-900/90 rounded-2xl border border-slate-800 p-4 shadow-xl">
          <div className="flex flex-col md:flex-row md:items-center justify-between gap-3">
            <div className="flex items-center space-x-3">
              <div className="p-2 bg-indigo-500/10 text-indigo-400 rounded-lg border border-indigo-500/20">
                <FolderGit2 className="w-5 h-5" />
              </div>
              <div>
                <h3 className="text-xs font-mono font-semibold uppercase tracking-wider text-slate-300">
                  Target Git Repository Remote Setup
                </h3>
                <p className="text-xs text-slate-400">
                  Initial commit commands targeting origin repository
                </p>
              </div>
            </div>

            <div className="flex items-center gap-2 overflow-x-auto bg-slate-950 p-2 rounded-xl border border-slate-800 text-xs font-mono text-emerald-400">
              <span>echo "# toolchain-factory" &gt;&gt; README.md &amp;&amp; git init &amp;&amp; git push origin main</span>
              <button
                onClick={() => copyToClipboard(`echo "# toolchain-factory" >> README.md\ngit init\ngit add README.md\ngit commit -m "first commit"\ngit branch -M main\ngit remote add origin https://github.com/kolberz/toolchain-factory.git\ngit push -u origin main`, 'git-commands')}
                className="px-2.5 py-1 bg-slate-800 hover:bg-slate-700 text-slate-200 text-xs rounded-lg transition-colors flex items-center gap-1 shrink-0"
              >
                {copiedCommand === 'git-commands' ? <Check className="w-3.5 h-3.5 text-emerald-400" /> : <Copy className="w-3.5 h-3.5" />}
                <span>{copiedCommand === 'git-commands' ? 'Copied!' : 'Copy Shell Script'}</span>
              </button>
            </div>
          </div>
        </section>

        {/* TAB 1: ARCHITECT CONFIGURATOR */}
        {activeTab === 'architect' && (
          <div className="space-y-8">
            {/* Presets Grid */}
            <div>
              <div className="flex items-center justify-between mb-4">
                <div>
                  <h2 className="text-lg font-bold text-white flex items-center gap-2">
                    <Zap className="w-5 h-5 text-amber-400" />
                    Featured Production Stack Presets
                  </h2>
                  <p className="text-xs text-slate-400">Select a pre-validated toolchain preset or customize individual modules below.</p>
                </div>
              </div>

              <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
                {TOOLCHAIN_PRESETS.map((preset) => {
                  const isSelected = selectedPresetId === preset.id;
                  return (
                    <div
                      key={preset.id}
                      onClick={() => handleSelectPreset(preset)}
                      className={`cursor-pointer p-5 rounded-2xl border transition-all ${
                        isSelected
                          ? 'bg-gradient-to-b from-indigo-950/60 to-slate-900 border-indigo-500/80 shadow-lg shadow-indigo-500/10 ring-1 ring-indigo-500/50'
                          : 'bg-slate-900/60 border-slate-800/80 hover:border-slate-700 hover:bg-slate-900/90'
                      }`}
                    >
                      <div className="flex items-center justify-between mb-2">
                        <span className="text-xs font-semibold px-2.5 py-0.5 rounded-full bg-indigo-500/10 text-indigo-400 border border-indigo-500/20">
                          {preset.badge}
                        </span>
                        {isSelected && <CheckCircle2 className="w-5 h-5 text-indigo-400" />}
                      </div>
                      <h3 className="text-base font-semibold text-white mb-1">{preset.name}</h3>
                      <p className="text-xs text-indigo-300 font-medium mb-2">{preset.tagline}</p>
                      <p className="text-xs text-slate-400 line-clamp-2 leading-relaxed">{preset.description}</p>
                    </div>
                  );
                })}
              </div>
            </div>

            {/* Config Modifiers */}
            <div className="bg-slate-900/80 border border-slate-800 rounded-2xl p-6">
              <h2 className="text-lg font-bold text-white mb-4 flex items-center gap-2">
                <Wrench className="w-5 h-5 text-indigo-400" />
                Custom Stack Composition
              </h2>

              <div className="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-3 gap-6">
                {/* Project Details */}
                <div className="space-y-2">
                  <label className="text-xs font-mono uppercase text-slate-400 font-semibold">Project Name</label>
                  <input
                    type="text"
                    value={config.projectName}
                    onChange={(e) => setConfig({ ...config, projectName: e.target.value })}
                    className="w-full bg-slate-950 border border-slate-800 rounded-xl px-3.5 py-2 text-sm text-white focus:outline-none focus:border-indigo-500"
                  />
                </div>

                {/* Framework */}
                <div className="space-y-2">
                  <label className="text-xs font-mono uppercase text-slate-400 font-semibold">Framework / Engine</label>
                  <select
                    value={config.framework}
                    onChange={(e) => setConfig({ ...config, framework: e.target.value as any })}
                    className="w-full bg-slate-950 border border-slate-800 rounded-xl px-3.5 py-2 text-sm text-white focus:outline-none focus:border-indigo-500"
                  >
                    {FRAMEWORK_OPTIONS.map((f) => (
                      <option key={f.id} value={f.id}>{f.name}</option>
                    ))}
                  </select>
                </div>

                {/* Runtime */}
                <div className="space-y-2">
                  <label className="text-xs font-mono uppercase text-slate-400 font-semibold">Runtime Platform</label>
                  <select
                    value={config.runtime}
                    onChange={(e) => setConfig({ ...config, runtime: e.target.value as any })}
                    className="w-full bg-slate-950 border border-slate-800 rounded-xl px-3.5 py-2 text-sm text-white focus:outline-none focus:border-indigo-500"
                  >
                    {RUNTIME_OPTIONS.map((r) => (
                      <option key={r.id} value={r.id}>{r.name}</option>
                    ))}
                  </select>
                </div>

                {/* Bundler */}
                <div className="space-y-2">
                  <label className="text-xs font-mono uppercase text-slate-400 font-semibold">Bundler / Build Engine</label>
                  <select
                    value={config.bundler}
                    onChange={(e) => setConfig({ ...config, bundler: e.target.value as any })}
                    className="w-full bg-slate-950 border border-slate-800 rounded-xl px-3.5 py-2 text-sm text-white focus:outline-none focus:border-indigo-500"
                  >
                    {BUNDLER_OPTIONS.map((b) => (
                      <option key={b.id} value={b.id}>{b.name}</option>
                    ))}
                  </select>
                </div>

                {/* Testing */}
                <div className="space-y-2">
                  <label className="text-xs font-mono uppercase text-slate-400 font-semibold">Test Suite</label>
                  <select
                    value={config.testing}
                    onChange={(e) => setConfig({ ...config, testing: e.target.value as any })}
                    className="w-full bg-slate-950 border border-slate-800 rounded-xl px-3.5 py-2 text-sm text-white focus:outline-none focus:border-indigo-500"
                  >
                    {TESTING_OPTIONS.map((t) => (
                      <option key={t.id} value={t.id}>{t.name}</option>
                    ))}
                  </select>
                </div>

                {/* Linter */}
                <div className="space-y-2">
                  <label className="text-xs font-mono uppercase text-slate-400 font-semibold">Linter & Formatter</label>
                  <select
                    value={config.linter}
                    onChange={(e) => setConfig({ ...config, linter: e.target.value as any })}
                    className="w-full bg-slate-950 border border-slate-800 rounded-xl px-3.5 py-2 text-sm text-white focus:outline-none focus:border-indigo-500"
                  >
                    {LINTER_OPTIONS.map((l) => (
                      <option key={l.id} value={l.id}>{l.name}</option>
                    ))}
                  </select>
                </div>
              </div>

              {/* Toggles */}
              <div className="mt-6 pt-6 border-t border-slate-800 grid grid-cols-2 sm:grid-cols-4 gap-4 text-xs font-medium text-slate-300">
                <label className="flex items-center gap-2 cursor-pointer">
                  <input
                    type="checkbox"
                    checked={config.includeDockerCompose}
                    onChange={(e) => setConfig({ ...config, includeDockerCompose: e.target.checked })}
                    className="rounded border-slate-800 text-indigo-600 focus:ring-0"
                  />
                  <span>docker-compose.yml</span>
                </label>

                <label className="flex items-center gap-2 cursor-pointer">
                  <input
                    type="checkbox"
                    checked={config.includeMakefile}
                    onChange={(e) => setConfig({ ...config, includeMakefile: e.target.checked })}
                    className="rounded border-slate-800 text-indigo-600 focus:ring-0"
                  />
                  <span>Makefile</span>
                </label>

                <label className="flex items-center gap-2 cursor-pointer">
                  <input
                    type="checkbox"
                    checked={config.includeSetupScript}
                    onChange={(e) => setConfig({ ...config, includeSetupScript: e.target.checked })}
                    className="rounded border-slate-800 text-indigo-600 focus:ring-0"
                  />
                  <span>setup.sh script</span>
                </label>

                <label className="flex items-center gap-2 cursor-pointer">
                  <input
                    type="checkbox"
                    checked={config.includeReadmeBadges}
                    onChange={(e) => setConfig({ ...config, includeReadmeBadges: e.target.checked })}
                    className="rounded border-slate-800 text-indigo-600 focus:ring-0"
                  />
                  <span>README Badges</span>
                </label>
              </div>
            </div>

            {/* Live Compatibility Analysis */}
            <div className="bg-slate-900/80 border border-slate-800 rounded-2xl p-6">
              <h3 className="text-sm font-mono uppercase text-slate-400 font-semibold mb-3 flex items-center gap-2">
                <ShieldCheck className="w-4 h-4 text-emerald-400" />
                Live Toolchain Compatibility & Verification Status
              </h3>

              <div className="space-y-3">
                {compatibilityIssues.map((issue) => (
                  <div
                    key={issue.id}
                    className={`p-4 rounded-xl border flex items-start justify-between gap-4 ${
                      issue.severity === 'error'
                        ? 'bg-rose-500/10 border-rose-500/20 text-rose-300'
                        : issue.severity === 'warning'
                        ? 'bg-amber-500/10 border-amber-500/20 text-amber-300'
                        : 'bg-emerald-500/10 border-emerald-500/20 text-emerald-300'
                    }`}
                  >
                    <div className="space-y-1">
                      <div className="text-sm font-semibold flex items-center gap-2">
                        {issue.severity === 'error' && <AlertTriangle className="w-4 h-4 text-rose-400" />}
                        {issue.severity === 'warning' && <AlertTriangle className="w-4 h-4 text-amber-400" />}
                        {issue.severity === 'info' && <CheckCircle2 className="w-4 h-4 text-emerald-400" />}
                        <span>{issue.title}</span>
                      </div>
                      <p className="text-xs opacity-90 leading-relaxed">{issue.description}</p>
                    </div>

                    {issue.fixable && issue.fixAction && (
                      <button
                        onClick={() => setConfig(issue.fixAction!(config))}
                        className="px-3 py-1.5 bg-slate-900 hover:bg-slate-800 text-white text-xs font-medium rounded-lg border border-slate-700 shrink-0 transition-colors"
                      >
                        Auto-Fix Config
                      </button>
                    )}
                  </div>
                ))}
              </div>
            </div>
          </div>
        )}

        {/* TAB 2: LEAN 4 MODULAR SMALL ZIP STRATEGY & DIAGNOSTIC CAPSULES */}
        {activeTab === 'smallzips' && (
          <div className="space-y-8">
            {/* Modular Small ZIP Overview Header */}
            <div className="bg-gradient-to-r from-slate-900 via-indigo-950 to-slate-900 border border-indigo-500/30 rounded-2xl p-6 shadow-2xl relative overflow-hidden">
              <div className="max-w-3xl space-y-3">
                <div className="flex items-center gap-2">
                  <span className="px-3 py-1 rounded-full text-xs font-mono font-semibold bg-amber-500/20 text-amber-300 border border-amber-500/30 flex items-center gap-1.5">
                    <Sparkles className="w-3.5 h-3.5" />
                    Lean 4 + Mathlib Work-Unit Strategy
                  </span>
                </div>
                <h2 className="text-2xl font-bold text-white tracking-tight">
                  Modular Small ZIP Diagnostic & Repair Architecture
                </h2>
                <p className="text-xs text-slate-300 leading-relaxed">
                  Instead of treating a giant multi-gigabyte Lean + Mathlib environment as the only artifact, Toolchain Factory produces purpose-built, independently verifiable small ZIP packages for AI sandboxes (such as ChatGPT Linux sandboxes) to upload, inspect, execute, test, repair, and recombine.
                </p>
              </div>

              {/* Strategy Hierarchy Flow Diagram */}
              <div className="mt-6 pt-6 border-t border-slate-800/80 grid grid-cols-1 sm:grid-cols-5 gap-3 text-center text-xs font-mono">
                <div className="p-3 bg-slate-950/80 rounded-xl border border-slate-800">
                  <div className="text-slate-400 font-bold mb-1">1. Research Repo</div>
                  <div className="text-[10px] text-slate-500">Failing Lean files</div>
                </div>
                <div className="p-3 bg-amber-950/40 rounded-xl border border-amber-500/30 text-amber-300">
                  <div className="font-bold mb-1">2. Diagnostic Capsule</div>
                  <div className="text-[10px] opacity-80">Minimal failure ZIP</div>
                </div>
                <div className="p-3 bg-indigo-950/40 rounded-xl border border-indigo-500/30 text-indigo-300">
                  <div className="font-bold mb-1">3. AI Sandbox</div>
                  <div className="text-[10px] opacity-80">Offline compiler check</div>
                </div>
                <div className="p-3 bg-purple-950/40 rounded-xl border border-purple-500/30 text-purple-300">
                  <div className="font-bold mb-1">4. Repair Patch</div>
                  <div className="text-[10px] opacity-80">Verified tactic fix</div>
                </div>
                <div className="p-3 bg-emerald-950/40 rounded-xl border border-emerald-500/30 text-emerald-300">
                  <div className="font-bold mb-1">5. Lake Success</div>
                  <div className="text-[10px] opacity-80">Genuine evidence</div>
                </div>
              </div>
            </div>

            {/* Generated Small ZIP Units List */}
            <div className="space-y-4">
              <h3 className="text-base font-bold text-white flex items-center gap-2">
                <Package className="w-5 h-5 text-indigo-400" />
                Purpose-Built Small ZIP Units ({smallZipUnits.length})
              </h3>

              <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-5">
                {smallZipUnits.map((unit) => (
                  <div
                    key={unit.id}
                    className="bg-slate-900/80 border border-slate-800 rounded-2xl p-5 flex flex-col justify-between hover:border-slate-700 transition-all shadow-md"
                  >
                    <div>
                      <div className="flex items-center justify-between mb-3">
                        {renderClassificationBadge(unit.classification)}
                        <span className="text-[10px] font-mono text-slate-400">{unit.files.length} file(s)</span>
                      </div>
                      <h4 className="text-sm font-bold text-white mb-1.5">{unit.title}</h4>
                      <p className="text-xs text-slate-300 leading-relaxed mb-3">{unit.purpose}</p>

                      <div className="space-y-1 mb-4 text-[11px] font-mono text-slate-400 bg-slate-950 p-2.5 rounded-xl border border-slate-800">
                        <div className="text-slate-500 text-[10px] uppercase">Requires:</div>
                        {unit.requires.map((req, idx) => (
                          <div key={idx} className="flex items-center gap-1.5 text-indigo-300">
                            <ChevronRight className="w-3 h-3 text-indigo-400" />
                            <span>{req}</span>
                          </div>
                        ))}
                      </div>
                    </div>

                    <button
                      onClick={() => handleDownloadSmallZip(unit)}
                      className="w-full py-2 px-3 bg-slate-800 hover:bg-slate-700 text-white text-xs font-medium rounded-xl border border-slate-700 flex items-center justify-center gap-2 transition-colors"
                    >
                      <Download className="w-3.5 h-3.5 text-emerald-400" />
                      <span>Download {unit.filename}</span>
                    </button>
                  </div>
                ))}
              </div>
            </div>

            {/* Diagnostic Capsule Failure Studio */}
            <div className="bg-slate-900/80 border border-slate-800 rounded-2xl p-6">
              <div className="flex items-center justify-between mb-4">
                <div>
                  <h3 className="text-base font-bold text-white flex items-center gap-2">
                    <Bug className="w-5 h-5 text-amber-400" />
                    Create Custom Diagnostic Failure Capsule
                  </h3>
                  <p className="text-xs text-slate-400">
                    Paste a failing Lean proof snippet and error log to produce a minimal reproducible diagnostic ZIP.
                  </p>
                </div>

                <button
                  onClick={async () => {
                    const customUnitFiles: GeneratedFile[] = [
                      {
                        path: 'failing/CustomRepro.lean',
                        filename: 'CustomRepro.lean',
                        language: 'lean',
                        content: diagnosticCode,
                        description: 'Custom failing reproducer source file.',
                        zipClassification: 'DIAGNOSTIC'
                      },
                      {
                        path: 'compiler_error.log',
                        filename: 'compiler_error.log',
                        language: 'text',
                        content: diagnosticErrorLog,
                        description: 'Exact compiler output log.',
                        zipClassification: 'DIAGNOSTIC'
                      }
                    ];
                    await downloadProjectZip('lean-custom-diagnostic-capsule', customUnitFiles);
                  }}
                  className="px-4 py-2 bg-amber-600 hover:bg-amber-500 text-white text-xs font-semibold rounded-xl shadow-lg shadow-amber-600/20 flex items-center gap-1.5 transition-all"
                >
                  <Download className="w-4 h-4" />
                  <span>Export Diagnostic Capsule ZIP</span>
                </button>
              </div>

              <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
                <div className="space-y-2">
                  <label className="text-xs font-mono uppercase text-slate-400 font-semibold">
                    Failing Lean 4 Source (.lean)
                  </label>
                  <textarea
                    rows={8}
                    value={diagnosticCode}
                    onChange={(e) => setDiagnosticCode(e.target.value)}
                    className="w-full bg-slate-950 border border-slate-800 rounded-xl p-3 text-xs font-mono text-indigo-300 focus:outline-none focus:border-indigo-500 leading-relaxed"
                  />
                </div>

                <div className="space-y-2">
                  <label className="text-xs font-mono uppercase text-slate-400 font-semibold">
                    Lake Build Compiler Output Log
                  </label>
                  <textarea
                    rows={8}
                    value={diagnosticErrorLog}
                    onChange={(e) => setDiagnosticErrorLog(e.target.value)}
                    className="w-full bg-slate-950 border border-slate-800 rounded-xl p-3 text-xs font-mono text-amber-300 focus:outline-none focus:border-indigo-500 leading-relaxed"
                  />
                </div>
              </div>
            </div>
          </div>
        )}

        {/* TAB 3: GENERATED FILE TREE & CODE PREVIEW */}
        {activeTab === 'files' && (
          <div className="grid grid-cols-1 lg:grid-cols-4 gap-6">
            {/* File List Tree Sidebar */}
            <div className="lg:col-span-1 bg-slate-900/80 border border-slate-800 rounded-2xl p-4 h-[600px] flex flex-col">
              <h3 className="text-xs font-mono uppercase text-slate-400 font-semibold mb-3 flex items-center gap-2">
                <FolderGit2 className="w-4 h-4 text-indigo-400" />
                Generated Files ({generatedFiles.length})
              </h3>

              <div className="space-y-1 overflow-y-auto flex-1 pr-1 custom-scrollbar">
                {generatedFiles.map((file) => {
                  const isSelected = file.path === selectedFilePath;
                  return (
                    <button
                      key={file.path}
                      onClick={() => setSelectedFilePath(file.path)}
                      className={`w-full text-left px-3 py-2 rounded-xl text-xs font-mono transition-all flex items-center justify-between ${
                        isSelected
                          ? 'bg-indigo-600 text-white font-semibold shadow-md'
                          : 'text-slate-300 hover:bg-slate-800/80 hover:text-white'
                      }`}
                    >
                      <div className="truncate flex items-center gap-2">
                        <FileCode className="w-3.5 h-3.5 shrink-0 opacity-70" />
                        <span className="truncate">{file.path}</span>
                      </div>
                    </button>
                  );
                })}
              </div>
            </div>

            {/* Code Content Preview */}
            <div className="lg:col-span-3 bg-slate-900/80 border border-slate-800 rounded-2xl p-5 h-[600px] flex flex-col">
              <div className="flex items-center justify-between mb-4 pb-3 border-b border-slate-800">
                <div>
                  <h3 className="text-sm font-mono font-bold text-white flex items-center gap-2">
                    <FileCode className="w-4 h-4 text-indigo-400" />
                    {selectedFile.path}
                  </h3>
                  <p className="text-xs text-slate-400">{selectedFile.description}</p>
                </div>

                <button
                  onClick={() => copyToClipboard(selectedFile.content, selectedFile.path)}
                  className="px-3 py-1.5 bg-slate-800 hover:bg-slate-700 text-slate-200 text-xs rounded-xl border border-slate-700 transition-colors flex items-center gap-1.5"
                >
                  {copiedCommand === selectedFile.path ? <Check className="w-3.5 h-3.5 text-emerald-400" /> : <Copy className="w-3.5 h-3.5" />}
                  <span>{copiedCommand === selectedFile.path ? 'Copied' : 'Copy Code'}</span>
                </button>
              </div>

              <div className="flex-1 bg-slate-950 rounded-xl p-4 overflow-auto font-mono text-xs text-indigo-200 leading-relaxed border border-slate-800/80">
                <pre>{selectedFile.content}</pre>
              </div>
            </div>
          </div>
        )}

        {/* TAB 4: CI/CD PIPELINE SIMULATOR */}
        {activeTab === 'pipeline' && (
          <div className="space-y-6">
            <div className="bg-slate-900/80 border border-slate-800 rounded-2xl p-6">
              <div className="flex items-center justify-between mb-6">
                <div>
                  <h2 className="text-lg font-bold text-white flex items-center gap-2">
                    <Terminal className="w-5 h-5 text-emerald-400" />
                    CI/CD Workflow Pipeline Execution
                  </h2>
                  <p className="text-xs text-slate-400">
                    Simulate continuous integration matrix steps: static checks, test runner, container build, and cloud deploy.
                  </p>
                </div>

                <button
                  onClick={handleRunPipelineSim}
                  disabled={isRunningPipeline}
                  className="px-4 py-2 bg-indigo-600 hover:bg-indigo-500 disabled:opacity-50 text-white text-xs font-semibold rounded-xl shadow-lg shadow-indigo-600/20 flex items-center gap-2 transition-all"
                >
                  <Play className="w-4 h-4" />
                  <span>{isRunningPipeline ? 'Executing Pipeline...' : 'Run CI Pipeline'}</span>
                </button>
              </div>

              <div className="space-y-4">
                {pipelineSteps.map((step) => (
                  <div
                    key={step.id}
                    className="p-4 bg-slate-950 rounded-xl border border-slate-800 flex flex-col gap-2"
                  >
                    <div className="flex items-center justify-between">
                      <div className="flex items-center space-x-3">
                        <div className={`p-1.5 rounded-lg text-xs font-mono ${
                          step.status === 'success' ? 'bg-emerald-500/20 text-emerald-400' :
                          step.status === 'running' ? 'bg-indigo-500/20 text-indigo-400 animate-pulse' :
                          'bg-slate-800 text-slate-400'
                        }`}>
                          {step.status === 'success' ? <CheckCircle2 className="w-4 h-4" /> :
                           step.status === 'running' ? <RefreshCw className="w-4 h-4 animate-spin" /> :
                           <Terminal className="w-4 h-4" />}
                        </div>
                        <div>
                          <div className="text-sm font-semibold text-white">{step.name}</div>
                          <div className="text-xs font-mono text-slate-400">{step.command}</div>
                        </div>
                      </div>

                      <span className="text-xs font-mono text-slate-500">{step.estimatedTimeSec}s</span>
                    </div>

                    {step.logOutput.length > 0 && (
                      <div className="mt-2 pt-2 border-t border-slate-900 font-mono text-[11px] text-slate-400 space-y-1">
                        {step.logOutput.map((log, idx) => (
                          <div key={idx}>{log}</div>
                        ))}
                      </div>
                    )}
                  </div>
                ))}
              </div>
            </div>
          </div>
        )}

        {/* TAB 5: AI TOOLCHAIN ARCHITECT CHAT */}
        {activeTab === 'ai' && (
          <div className="bg-slate-900/80 border border-slate-800 rounded-2xl p-6 h-[650px] flex flex-col">
            <div className="flex items-center space-x-3 pb-4 border-b border-slate-800">
              <div className="p-2 bg-indigo-600/20 text-indigo-400 rounded-xl border border-indigo-500/30">
                <Sparkles className="w-5 h-5" />
              </div>
              <div>
                <h3 className="text-sm font-bold text-white">AI Toolchain Architect (Gemini Powered)</h3>
                <p className="text-xs text-slate-400">Ask questions regarding toolchain configuration, Lean 4 tactics, or Docker caching strategies.</p>
              </div>
            </div>

            {/* Messages Chat Output */}
            <div className="flex-1 overflow-y-auto my-4 space-y-4 pr-2 custom-scrollbar">
              {aiMessages.map((msg, index) => (
                <div
                  key={index}
                  className={`flex ${msg.sender === 'user' ? 'justify-end' : 'justify-start'}`}
                >
                  <div
                    className={`max-w-2xl p-4 rounded-2xl text-xs leading-relaxed ${
                      msg.sender === 'user'
                        ? 'bg-indigo-600 text-white rounded-br-none'
                        : 'bg-slate-950 text-slate-200 border border-slate-800 rounded-bl-none'
                    }`}
                  >
                    <pre className="font-sans whitespace-pre-wrap">{msg.text}</pre>
                  </div>
                </div>
              ))}
              {aiLoading && (
                <div className="flex justify-start">
                  <div className="p-3 bg-slate-950 rounded-2xl text-xs text-indigo-300 border border-slate-800 flex items-center gap-2">
                    <RefreshCw className="w-3.5 h-3.5 animate-spin" />
                    <span>Analyzing toolchain topology...</span>
                  </div>
                </div>
              )}
            </div>

            {/* Chat Input Bar */}
            <div className="flex items-center space-x-2 pt-2 border-t border-slate-800">
              <input
                type="text"
                placeholder="Ask about Lean 4 Mathlib imports, Docker caching, Vite plugins..."
                value={aiPrompt}
                onChange={(e) => setAiPrompt(e.target.value)}
                onKeyDown={(e) => e.key === 'Enter' && handleSendAiPrompt()}
                className="flex-1 bg-slate-950 border border-slate-800 rounded-xl px-4 py-2.5 text-xs text-white focus:outline-none focus:border-indigo-500"
              />
              <button
                onClick={handleSendAiPrompt}
                disabled={aiLoading}
                className="px-4 py-2.5 bg-indigo-600 hover:bg-indigo-500 disabled:opacity-50 text-white rounded-xl text-xs font-semibold flex items-center gap-1.5 transition-colors"
              >
                <Send className="w-3.5 h-3.5" />
                <span>Send</span>
              </button>
            </div>
          </div>
        )}
      </main>
    </div>
  );
}
