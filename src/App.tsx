import React, { useState, useMemo } from 'react';
import {
  Cpu, Zap, Shield, Flame, Atom, Code, Sparkles, Server, Activity, Box,
  Terminal, Palette, Layout, FileCode, CheckCircle2, Globe, Award, Eye,
  Minus, ShieldCheck, Container, GitBranch, Gitlab, Circle, Cloud, Triangle,
  Layers, Github, Download, Copy, Check, Play, Link, AlertTriangle, RefreshCw,
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
import { CertificationRunner } from './components/CertificationRunner';

export default function App() {
  // Navigation State
  const [activeTab, setActiveTab] = useState<'architect' | 'smallzips' | 'files' | 'pipeline' | 'ai' | 'backend' | 'certification'>('architect');
  
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

            <button
              onClick={() => setActiveTab('backend')}
              className={`px-3 py-1.5 rounded-lg text-xs font-medium transition-all flex items-center gap-1.5 ${
                activeTab === 'backend' ? 'bg-indigo-600 text-white shadow-sm' : 'text-slate-400 hover:text-slate-200'
              }`}
            >
              <Server className="w-3.5 h-3.5 text-emerald-400" />
              <span>Backend APIs</span>
            </button>

            <button
              onClick={() => setActiveTab('certification')}
              className={`px-3 py-1.5 rounded-lg text-xs font-medium transition-all flex items-center gap-1.5 ${
                activeTab === 'certification' ? 'bg-indigo-600 text-white shadow-sm' : 'text-slate-400 hover:text-slate-200'
              }`}
            >
              <ShieldCheck className="w-3.5 h-3.5 text-amber-400" />
              <span>Certification</span>
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
              <span>git remote add origin https://github.com/kolberz/Toolchain_factory.git &amp;&amp; git push origin main</span>
              <button
                onClick={() => copyToClipboard(`git init\ngit add README.md\ngit commit -m "first commit"\ngit branch -M main\ngit remote add origin https://github.com/kolberz/Toolchain_factory.git\ngit push -u origin main`, 'git-commands')}
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

            {/* Upstream Provenance & Forensic Audit Matrix */}
            <div className="bg-slate-900/90 border border-slate-800 rounded-2xl p-6 space-y-6 shadow-xl">
              <div className="flex flex-col md:flex-row md:items-center justify-between gap-4 border-b border-slate-800 pb-4">
                <div>
                  <div className="flex items-center gap-2 mb-1">
                    <ShieldCheck className="w-5 h-5 text-indigo-400" />
                    <h3 className="text-base font-bold text-white tracking-tight">
                      Lean 4 v4.32.2 Upstream Provenance & Forensic Audit Matrix
                    </h3>
                  </div>
                  <p className="text-xs text-slate-400">
                    Independent GitHub verification separating authenticated upstream anchors from simulated mock payloads.
                  </p>
                </div>

                <div className="flex items-center gap-2">
                  <span className="px-3 py-1 bg-emerald-500/10 text-emerald-400 border border-emerald-500/30 rounded-full text-xs font-mono font-semibold">
                    Upstream Provenance: VERIFIED
                  </span>
                </div>
              </div>

              {/* Upgraded Final Verdict Alert Banner */}
              <div className="p-4 bg-rose-500/10 border border-rose-500/30 rounded-xl text-rose-300 text-xs leading-relaxed space-y-1">
                <div className="font-bold flex items-center gap-2 text-rose-200">
                  <AlertTriangle className="w-4 h-4 text-rose-400 shrink-0" />
                  <span>FORENSIC VERDICT</span>
                </div>
                <p className="font-mono text-[11px] leading-relaxed">
                  <strong>FORENSICALLY CONFIRMED:</strong> The previous 1.8 KB ZIP collection is not an authentic Lean 4.32.2 + Mathlib v4.32.2 distribution and cannot serve as evidence of successful Lean compilation or Lake execution.
                </p>
              </div>

              {/* Full Certificate Formula Banner */}
              <div className="p-5 bg-gradient-to-r from-indigo-950/80 via-slate-900 to-purple-950/80 border border-indigo-500/40 rounded-2xl space-y-4 shadow-2xl">
                <div className="flex flex-col sm:flex-row sm:items-center justify-between gap-3">
                  <div className="flex items-center gap-2">
                    <CheckCircle2 className="w-5 h-5 text-indigo-400" />
                    <h4 className="text-sm font-bold text-white uppercase tracking-wider font-mono">
                      Current Certification State
                    </h4>
                  </div>
                  <span className="px-2.5 py-1 bg-amber-500/10 text-amber-300 border border-amber-500/30 rounded-lg text-[10px] font-mono font-bold">
                    STATUS: IMMUTABLE UPSTREAM ANCHORS VERIFIED. FACTORY-PIPELINE EXECUTION CERTIFICATION REQUIRES ATTACHED RUN EVIDENCE.
                  </span>
                </div>

                <div className="grid grid-cols-1 md:grid-cols-3 gap-3">
                  <div className="p-3 bg-slate-950/90 rounded-xl border border-emerald-500/30 font-mono text-center text-xs text-emerald-300 shadow-inner flex flex-col justify-center gap-1">
                    <span className="text-slate-500 font-bold">\[</span>
                    <span className="border border-emerald-500/60 rounded p-1.5 bg-emerald-950/40 inline-block font-bold">
                      {"\\text{MANIFEST ANCHORS: VERIFIED}"}
                    </span>
                    <span className="text-slate-500 font-bold">\]</span>
                  </div>

                  <div className="p-3 bg-slate-950/90 rounded-xl border border-indigo-500/30 font-mono text-center text-xs text-indigo-300 shadow-inner flex flex-col justify-center gap-1">
                    <span className="text-slate-500 font-bold">\[</span>
                    <span className="border border-indigo-500/60 rounded p-1.5 bg-indigo-950/40 inline-block font-bold">
                      {"\\text{EXECUTION GATE SPECIFICATION: VALID}"}
                    </span>
                    <span className="text-slate-500 font-bold">\]</span>
                  </div>

                  <div className="p-3 bg-slate-950/90 rounded-xl border border-amber-500/30 font-mono text-center text-xs text-amber-300 shadow-inner flex flex-col justify-center gap-1">
                    <span className="text-slate-500 font-bold">\[</span>
                    <span className="border border-amber-500/60 rounded p-1.5 bg-amber-950/40 inline-block font-bold">
                      {"\\text{EXECUTION GATE RESULTS: ASSERTED, NOT INDEPENDENTLY VERIFIED}"}
                    </span>
                    <span className="text-slate-500 font-bold">\]</span>
                  </div>
                </div>

                <div className="mt-4 p-3 bg-slate-900/60 rounded-xl border border-slate-700/50">
                  <div className="flex flex-col gap-3">
                    <p className="text-xs text-slate-400 font-mono">The final certificate computation:</p>
                    <div className="p-3 bg-slate-950/90 rounded-lg border border-indigo-500/20 font-mono text-center text-xs md:text-sm text-indigo-200 overflow-x-auto shadow-inner">
                      <span className="text-slate-500 font-bold mr-2">\[</span>
                      <span className="border-2 border-indigo-500/40 rounded-lg px-4 py-2 bg-indigo-950/20 inline-flex flex-wrap items-center justify-center gap-2 font-bold text-white">
                        <span className="text-indigo-300">{"\\text{FINAL VERIFIED}"}</span>
                        <span className="text-slate-400">{"\\iff"}</span>
                        <span className="text-emerald-400">{"P"}</span>
                        <span className="text-slate-400">{"\\land"}</span>
                        <span className="text-emerald-400">{"E"}</span>
                        <span className="text-slate-400">{"\\land"}</span>
                        <span className="text-emerald-400">{"O"}</span>
                      </span>
                      <span className="text-slate-500 font-bold ml-2">\]</span>
                    </div>
                    
                    <div className="grid grid-cols-1 md:grid-cols-3 gap-2 text-[10px] text-slate-400 font-mono bg-slate-950 p-2 rounded-lg border border-slate-800">
                      <div className="bg-slate-900 px-2 py-1.5 rounded"><span className="text-emerald-400 font-bold">P</span> = provenance verified</div>
                      <div className="bg-slate-900 px-2 py-1.5 rounded"><span className="text-emerald-400 font-bold">E</span> = all execution discrimination gates verified</div>
                      <div className="bg-slate-900 px-2 py-1.5 rounded"><span className="text-emerald-400 font-bold">O</span> = both independent offline reconstructions verified</div>
                    </div>
                  </div>
                </div>

                {/* Cryptographic Certification Chain */}
                <div className="mt-4 p-4 bg-slate-950/80 rounded-xl border border-indigo-500/30 flex flex-col gap-3">
                  <div className="text-xs font-mono font-semibold text-slate-300 uppercase tracking-wider flex items-center gap-1.5">
                    <Link className="w-4 h-4 text-indigo-400" />
                    Cryptographic Certification Chain
                  </div>
                  <div className="flex flex-wrap items-center justify-center gap-2 text-[10px] font-mono text-indigo-300 bg-indigo-950/30 p-3 rounded-lg border border-indigo-500/20 shadow-inner">
                    <span className="font-bold px-2 py-1 bg-slate-900 rounded border border-slate-700">Upstream Anchor</span>
                    <span className="text-indigo-500">→</span>
                    <span className="font-bold px-2 py-1 bg-slate-900 rounded border border-slate-700">Artifact</span>
                    <span className="text-indigo-500">→</span>
                    <span className="font-bold px-2 py-1 bg-slate-900 rounded border border-slate-700">Execution Evidence</span>
                    <span className="text-indigo-500">→</span>
                    <span className="font-bold px-2 py-1 bg-slate-900 rounded border border-slate-700">Gate Certificate</span>
                    <span className="text-indigo-500">→</span>
                    <span className="font-bold px-2 py-1 bg-slate-900 rounded border border-slate-700">Reconstruction Certificate</span>
                    <span className="text-indigo-500">→</span>
                    <span className="font-bold px-2 py-1 bg-indigo-600 rounded border border-indigo-400 text-white shadow-lg shadow-indigo-500/20">Final Certificate</span>
                  </div>
                </div>

                {/* Certificate Invalidation Rule */}
                <div className="mt-4 p-4 bg-rose-950/30 rounded-xl border border-rose-500/30 flex flex-col gap-3">
                  <div className="text-xs font-mono font-semibold text-rose-300 uppercase tracking-wider flex items-center gap-1.5">
                    <AlertTriangle className="w-4 h-4 text-rose-400" />
                    Automatic Invalidation Rule
                  </div>
                  <p className="text-[11px] text-rose-200/70 font-mono">
                    If any upstream anchor, artifact hash, execution evidence, or expected predicate changes, dependent certificates immediately fallback to STALE / REQUIRES REVALIDATION.
                  </p>
                  <div className="flex items-center justify-center text-[11px] md:text-xs text-rose-300 font-mono bg-rose-950/50 p-3 rounded-lg border border-rose-500/20 shadow-inner overflow-x-auto">
                    <span className="text-slate-500 font-bold mr-2">\[</span>
                    <span className="bg-slate-900 px-3 py-1.5 rounded border border-rose-500/40 inline-flex flex-wrap items-center gap-1.5 font-bold">
                      <span className="text-rose-400">{"\\Delta"}</span>
                      <span className="text-slate-400">{"("}</span>
                      <span className="text-cyan-300">{"\\text{dependency}"}</span>
                      <span className="text-slate-400">{")"}</span>
                      <span className="text-rose-400">{"\\Rightarrow"}</span>
                      <span className="text-rose-400">{"\\neg\\text{VALID}"}</span>
                      <span className="text-slate-400">{"("}</span>
                      <span className="text-cyan-300">{"\\text{dependent certificate}"}</span>
                      <span className="text-slate-400">{")"}</span>
                    </span>
                    <span className="text-slate-500 font-bold ml-2">\]</span>
                  </div>
                </div>
              </div>

              {/* GitHub App Connector Diagnostic Banner */}
              <div className="p-5 bg-slate-950/90 rounded-2xl border border-blue-500/40 space-y-4 shadow-xl font-mono">
                <div className="flex flex-col sm:flex-row sm:items-center justify-between gap-2 border-b border-blue-500/20 pb-3">
                  <div className="flex items-center gap-2">
                    <Github className="w-5 h-5 text-blue-400" />
                    <h4 className="text-sm font-bold text-white uppercase tracking-wider">
                      GitHub App Connector Diagnostic & Access Gate
                    </h4>
                  </div>
                  <span className="px-2.5 py-1 bg-amber-500/10 text-amber-300 border border-amber-500/30 rounded-lg text-[10px] font-bold self-start sm:self-auto">
                    STATUS: TEST BLOCKED: REPOSITORY ACCESS REQUIRED
                  </span>
                </div>
                
                {/* 3-Tier Layer Distinction Equation */}
                <div className="flex items-center justify-center text-[11px] md:text-xs text-blue-300 bg-blue-950/40 p-3 rounded-xl border border-blue-500/30 shadow-inner overflow-x-auto">
                  <span className="text-slate-500 font-bold mr-2">\[</span>
                  <span className="bg-slate-900 px-3 py-1.5 rounded-lg border border-blue-500/40 inline-flex flex-wrap items-center gap-2 font-bold">
                    <span className="text-emerald-400">{"\\text{@GitHub mention resolved}"}</span>
                    <span className="text-slate-400">{"\\neq"}</span>
                    <span className="text-rose-400">{"\\text{GitHub App installed}"}</span>
                    <span className="text-slate-400">{"\\neq"}</span>
                    <span className="text-rose-400">{"\\text{Repository authorized}"}</span>
                  </span>
                  <span className="text-slate-500 font-bold ml-2">\]</span>
                </div>

                {/* 5-Step Diagnostic Gating Pipeline */}
                <div className="space-y-2 pt-1">
                  <div className="text-[10px] text-slate-400 uppercase font-bold flex justify-between items-center">
                    <span>Connector Pipeline Verification Gates</span>
                    <span>Gate Status</span>
                  </div>
                  <div className="grid grid-cols-1 md:grid-cols-5 gap-2 text-[10px]">
                    <div className="p-2.5 bg-slate-900/80 rounded-lg border border-emerald-500/30 flex flex-col justify-between gap-1">
                      <span className="text-slate-400 font-bold">1. Mention</span>
                      <span className="text-emerald-300 truncate">MENTION_CONNECTED</span>
                      <span className="px-1.5 py-0.5 bg-emerald-500/20 text-emerald-400 rounded text-[9px] font-bold w-max">PASS</span>
                    </div>
                    <div className="p-2.5 bg-slate-900/80 rounded-lg border border-rose-500/30 flex flex-col justify-between gap-1">
                      <span className="text-slate-400 font-bold">2. Installation</span>
                      <span className="text-rose-300 truncate">APP_INSTALLATION</span>
                      <span className="px-1.5 py-0.5 bg-rose-500/20 text-rose-400 rounded text-[9px] font-bold w-max">MISSING</span>
                    </div>
                    <div className="p-2.5 bg-slate-900/80 rounded-lg border border-rose-500/30 flex flex-col justify-between gap-1">
                      <span className="text-slate-400 font-bold">3. Repository</span>
                      <span className="text-rose-300 truncate">kolberz/Toolchain_factory</span>
                      <span className="px-1.5 py-0.5 bg-rose-500/20 text-rose-400 rounded text-[9px] font-bold w-max">404 NOT FOUND</span>
                    </div>
                    <div className="p-2.5 bg-slate-900/80 rounded-lg border border-slate-800 flex flex-col justify-between gap-1 opacity-60">
                      <span className="text-slate-500 font-bold">4. Source</span>
                      <span className="text-slate-500 truncate">SOURCE_FETCHED</span>
                      <span className="px-1.5 py-0.5 bg-slate-800 text-slate-400 rounded text-[9px] font-bold w-max">BLOCKED</span>
                    </div>
                    <div className="p-2.5 bg-slate-900/80 rounded-lg border border-slate-800 flex flex-col justify-between gap-1 opacity-60">
                      <span className="text-slate-500 font-bold">5. Execution</span>
                      <span className="text-slate-500 truncate">IMPLEMENTATION_TESTED</span>
                      <span className="px-1.5 py-0.5 bg-slate-800 text-slate-400 rounded text-[9px] font-bold w-max">BLOCKED</span>
                    </div>
                  </div>
                </div>

                {/* Evidence Chain Formula & State Function Matrix */}
                <div className="p-3 bg-slate-900/60 rounded-xl border border-slate-800 space-y-2">
                  <div className="text-[10px] text-slate-400 font-semibold uppercase flex justify-between">
                    <span>Connector Diagnostic Evidence Chain</span>
                    <span className="text-indigo-400">UI Status = f(Connector Evidence)</span>
                  </div>
                  <div className="p-2 bg-slate-950 rounded-lg border border-slate-800 text-[10px] md:text-xs text-indigo-200 overflow-x-auto text-center space-y-2">
                    <div>
                      <span className="text-slate-500 font-bold mr-1">\[</span>
                      <span className="inline-flex flex-wrap items-center justify-center gap-1.5 font-bold">
                        <span className="text-emerald-400">{"\\text{Connector identity}"}</span>
                        <span className="text-slate-400">+</span>
                        <span className="text-rose-400">{"\\text{permission evidence}"}</span>
                        <span className="text-slate-400">+</span>
                        <span className="text-rose-400">{"\\text{repository resolution}"}</span>
                        <span className="text-slate-400">+</span>
                        <span className="text-slate-500">{"\\text{source inspection}"}</span>
                        <span className="text-slate-400">+</span>
                        <span className="text-slate-500">{"\\text{execution evidence}"}</span>
                      </span>
                      <span className="text-slate-500 font-bold ml-1">\]</span>
                    </div>

                    <div className="pt-2 border-t border-slate-800/80 flex flex-wrap items-center justify-center gap-3 text-[10px] text-slate-300 font-mono">
                      <span className="bg-slate-900 px-2 py-1 rounded border border-slate-800"><span className="text-emerald-400 font-bold">M</span> = PASS</span>
                      <span className="bg-slate-900 px-2 py-1 rounded border border-slate-800"><span className="text-rose-400 font-bold">A</span> = MISSING</span>
                      <span className="bg-slate-900 px-2 py-1 rounded border border-slate-800"><span className="text-rose-400 font-bold">R</span> = 404 / UNRESOLVED</span>
                      <span className="bg-slate-900 px-2 py-1 rounded border border-slate-800"><span className="text-slate-500 font-bold">S</span> = BLOCKED</span>
                      <span className="bg-slate-900 px-2 py-1 rounded border border-slate-800"><span className="text-slate-500 font-bold">T</span> = BLOCKED</span>
                    </div>
                  </div>
                </div>

                {/* Automatic Revalidation Formula */}
                <div className="p-3 bg-blue-950/40 rounded-xl border border-blue-500/30 space-y-1">
                  <div className="text-[10px] text-blue-300 font-semibold uppercase">Revalidation Trigger Formula</div>
                  <div className="text-[10px] md:text-xs text-blue-200 font-mono text-center overflow-x-auto py-1">
                    <span className="text-slate-500 font-bold mr-1">\[</span>
                    <span className="bg-slate-900 px-2.5 py-1 rounded border border-blue-500/30 inline-flex flex-wrap items-center gap-1.5 font-bold">
                      <span className="text-blue-300">{"\\Delta(\\text{repository access})"}</span>
                      <span className="text-slate-400">{"\\Rightarrow"}</span>
                      <span className="text-amber-300">{"\\text{invalidate 404}"}</span>
                      <span className="text-slate-400">{"\\Rightarrow"}</span>
                      <span className="text-amber-300">{"\\text{REVALIDATION REQUIRED}"}</span>
                      <span className="text-slate-400">{"\\Rightarrow"}</span>
                      <span className="text-emerald-400">{"\\text{repository rediscovery}"}</span>
                    </span>
                    <span className="text-slate-500 font-bold ml-1">\]</span>
                  </div>
                </div>

                <p className="text-[11px] text-blue-200/80 leading-relaxed bg-blue-950/30 p-3 rounded-xl border border-blue-500/20">
                  <strong className="text-blue-300">Actionable Access Fix:</strong> Grant the GitHub app access to the repository containing <span className="text-blue-300">kolberz/Toolchain_factory</span>. Upon access grant, the diagnostic panel will automatically transition from 404 to <span className="text-amber-300">REVALIDATION REQUIRED</span> and trigger repository discovery.
                </p>
              </div>

              {/* MANIFEST_ANCHORS & Verification Hierarchy Grid */}
              <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
                {/* MANIFEST_ANCHORS Code Box & Mandatory Assertions */}
                <div className="space-y-4">
                  <div className="space-y-2">
                    <div className="flex items-center justify-between">
                      <span className="text-xs font-mono font-semibold text-slate-300 uppercase tracking-wider flex items-center gap-1.5">
                        <Code className="w-3.5 h-3.5 text-indigo-400" />
                        MANIFEST_ANCHORS Reference Point
                      </span>
                      <span className="text-[10px] font-mono text-emerald-400 font-bold">Immutable Anchor</span>
                    </div>
                    <pre className="bg-slate-950 p-4 rounded-xl border border-slate-800 text-indigo-300 text-[11px] font-mono overflow-x-auto leading-relaxed">
{`MANIFEST_ANCHORS = {
    "mathlib_tag": "v4.32.2",
    "mathlib_commit": "905b95818eb32af7874a58b427f50c1711a5e96c",
    "lean_toolchain": "leanprover/lean4:v4.32.2",

    "release_artifact": "lean-4.32.2-linux.tar.zst",
    "official_release_sha256":
        "5f2069e6f5db73780f374ccb49ce8ea649aa20a0cebf0116816744c999ce72aa",

    "official_release_bytes": 563_991_635,

    # Sanity/fraud-detection threshold only.
    "expected_min_bytes": 500_000_000,

    "architecture": "linux-x86_64",
}`}
                    </pre>
                  </div>

                  {/* Pre-Execution Mandatory Assertion Rules */}
                  <div className="space-y-2">
                    <div className="flex items-center justify-between">
                      <span className="text-xs font-mono font-semibold text-amber-300 uppercase tracking-wider flex items-center gap-1.5">
                        <ShieldCheck className="w-3.5 h-3.5 text-amber-400" />
                        Mandatory Pre-Execution Assertions
                      </span>
                      <span className="text-[10px] font-mono text-slate-400">Phase 1 Gate</span>
                    </div>
                    <pre className="bg-slate-950 p-3.5 rounded-xl border border-amber-500/30 text-amber-300 text-[11px] font-mono overflow-x-auto leading-relaxed space-y-1">
{`assert actual_sha256 == MANIFEST_ANCHORS["official_release_sha256"]
assert actual_bytes == MANIFEST_ANCHORS["official_release_bytes"]
assert mathlib_commit == MANIFEST_ANCHORS["mathlib_commit"]
assert lean_toolchain == MANIFEST_ANCHORS["lean_toolchain"]`}
                    </pre>
                  </div>
                </div>

                {/* Execution Gates Matrix */}
                <div className="space-y-4 font-mono text-xs">
                  <div className="flex flex-col sm:flex-row sm:items-center justify-between gap-2 border-b border-slate-800 pb-3">
                    <span className="text-xs font-semibold text-slate-300 uppercase tracking-wider flex items-center gap-1.5">
                      <Terminal className="w-3.5 h-3.5 text-emerald-400" />
                      Execution Discrimination Gates Evidence
                    </span>
                    <span className="px-2 py-0.5 bg-amber-500/10 text-amber-300 border border-amber-500/30 rounded font-bold text-[10px]">
                      AWAITING RUN EVIDENCE
                    </span>
                  </div>

                  {/* Gate Status Function Definition */}
                  <div className="p-3 bg-slate-950/90 rounded-lg border border-slate-800 shadow-inner overflow-x-auto">
                    <div className="text-[10px] text-slate-500 uppercase font-bold mb-2">Gate Certificate Computation</div>
                    <div className="flex items-center gap-2 text-[11px] md:text-xs">
                      <span className="text-slate-500 font-bold">\[</span>
                      <span className="text-white bg-slate-900 px-3 py-1.5 rounded border border-slate-700 inline-flex flex-wrap items-center gap-1.5">
                        <span className="text-indigo-400">{"\\text{GateStatus}"}</span>
                        <span className="text-slate-400">{"="}</span>
                        <span className="text-emerald-400">{"f"}</span><span className="text-slate-400">{"("}</span>
                        <span className="text-cyan-300">{"\\text{command}"}</span>,
                        <span className="text-cyan-300">{"\\text{executable hash}"}</span>,
                        <span className="text-cyan-300">{"\\text{exit code}"}</span>,
                        <span className="text-cyan-300">{"\\text{stdout/stderr}"}</span>,
                        <span className="text-cyan-300">{"\\text{reconstruction ID}"}</span>,
                        <span className="text-cyan-300">{"\\text{artifact hashes}"}</span>
                        <span className="text-slate-400">{")"}</span>
                      </span>
                      <span className="text-slate-500 font-bold">\]</span>
                    </div>
                  </div>

                  <div className="grid grid-cols-1 gap-3">
                    {[
                      { test: 'valid Lean', req: 'PASS', cmd: 'lean ValidProof.lean' },
                      { test: 'invalid syntax', req: 'FAIL', cmd: 'lean SyntaxError.lean' },
                      { test: 'false proof', req: 'FAIL', cmd: 'lean FalseProof.lean' },
                      { test: 'missing import', req: 'FAIL', cmd: 'lean MissingImport.lean' },
                      { test: 'import Mathlib', req: 'PASS', cmd: 'lean ImportMathlib.lean' },
                      { test: 'unknown lake command', req: 'FAIL', cmd: 'lake fake_cmd' },
                      { test: 'lake build', req: 'PASS', cmd: 'lake build' },
                      { test: 'fresh offline reconstruction', req: 'PASS', cmd: 'bash reconstruct_1.sh' },
                      { test: 'second offline reconstruction', req: 'PASS', cmd: 'bash reconstruct_2.sh' }
                    ].map((gate, i) => (
                      <div key={i} className="bg-slate-950 rounded-xl border border-slate-800 p-3 flex flex-col gap-3">
                        <div className="flex justify-between items-center border-b border-slate-800/60 pb-2">
                          <span className="text-slate-200 font-bold">{gate.test}</span>
                          <span className={`px-2 py-0.5 rounded font-bold text-[10px] ${gate.req === 'PASS' ? 'bg-emerald-500/10 text-emerald-400 border border-emerald-500/20' : 'bg-rose-500/10 text-rose-400 border border-rose-500/20'}`}>
                            Required: {gate.req}
                          </span>
                        </div>

                        <div className="grid grid-cols-1 md:grid-cols-2 gap-3 text-[10px]">
                          <div className="space-y-1">
                            <div className="text-slate-500 font-semibold uppercase">Command</div>
                            <div className="text-indigo-300 font-mono bg-slate-900/50 px-2 py-1.5 rounded truncate border border-slate-800/50">{gate.cmd}</div>
                          </div>
                          <div className="space-y-1">
                            <div className="text-slate-500 font-semibold uppercase">Executable Hash</div>
                            <div className="text-slate-400 font-mono bg-slate-900/50 px-2 py-1.5 rounded truncate border border-slate-800/50 italic">Pending Run Evidence</div>
                          </div>
                          <div className="space-y-1">
                            <div className="text-slate-500 font-semibold uppercase">Exit Code & Timestamp</div>
                            <div className="text-slate-400 font-mono bg-slate-900/50 px-2 py-1.5 rounded truncate border border-slate-800/50 italic">--</div>
                          </div>
                          <div className="space-y-1">
                            <div className="text-slate-500 font-semibold uppercase">Reconstruction ID</div>
                            <div className="text-slate-400 font-mono bg-slate-900/50 px-2 py-1.5 rounded truncate border border-slate-800/50 italic">--</div>
                          </div>
                          <div className="space-y-1 md:col-span-2">
                            <div className="text-slate-500 font-semibold uppercase text-amber-400/80">Evidence Bundle SHA-256 (Immutable Record)</div>
                            <div className="text-amber-200/50 font-mono bg-amber-950/20 px-2 py-1.5 rounded truncate border border-amber-500/20 italic">Awaiting certification...</div>
                          </div>
                        </div>

                        <div className="space-y-1 pt-1">
                          <div className="text-slate-500 font-semibold uppercase text-[10px]">Output (STDOUT / STDERR)</div>
                          <div className="text-slate-500 font-mono bg-slate-900/50 p-2.5 rounded text-[10px] italic border border-slate-800/50">
                            Awaiting attached run evidence...
                          </div>
                        </div>
                      </div>
                    ))}
                  </div>
                </div>
              </div>

              {/* Immutable Upstream Anchors Cards */}
              <div className="grid grid-cols-1 md:grid-cols-3 gap-3 text-xs font-mono">
                <div className="p-3.5 bg-slate-950 rounded-xl border border-slate-800 space-y-1">
                  <div className="text-slate-400 text-[10px] uppercase font-semibold">Mathlib Tag v4.32.2 Commit</div>
                  <div className="text-indigo-300 font-bold truncate">905b95818eb32af7874a58b427f50c1711a5e96c</div>
                </div>

                <div className="p-3.5 bg-slate-950 rounded-xl border border-slate-800 space-y-1">
                  <div className="text-slate-400 text-[10px] uppercase font-semibold">Toolchain Specification</div>
                  <div className="text-indigo-300 font-bold truncate">leanprover/lean4:v4.32.2</div>
                </div>

                <div className="p-3.5 bg-slate-950 rounded-xl border border-slate-800 space-y-1">
                  <div className="text-slate-400 text-[10px] uppercase font-semibold">Official Linux Lean Release Artifact</div>
                  <div className="text-emerald-300 font-bold truncate">lean-4.32.2-linux.tar.zst (538 MiB)</div>
                  <div className="text-[10px] text-slate-500 truncate">SHA256: 5f2069e6f5db...99ce72aa</div>
                </div>
              </div>

              {/* Comparative Audit Matrix Table */}
              <div className="overflow-x-auto rounded-xl border border-slate-800 bg-slate-950">
                <table className="w-full text-left border-collapse text-xs">
                  <thead>
                    <tr className="border-b border-slate-800 bg-slate-900/60 font-mono text-slate-400 text-[11px] uppercase">
                      <th className="p-3">Property / Claim</th>
                      <th className="p-3">Official Upstream Lean 4.32.2 + Mathlib v4.32.2</th>
                      <th className="p-3">Earlier Simulated Payload (1.8 KB)</th>
                      <th className="p-3">Forensic Audit Verdict</th>
                    </tr>
                  </thead>
                  <tbody className="divide-y divide-slate-800/60 font-mono text-[11px]">
                    <tr className="hover:bg-slate-900/30 transition-colors">
                      <td className="p-3 font-semibold text-white">Mathlib Version Tag</td>
                      <td className="p-3 text-emerald-400">v4.32.2 @ 905b95818e...</td>
                      <td className="p-3 text-slate-400">Simulated 42-byte tree</td>
                      <td className="p-3 text-emerald-400 font-bold">✅ CONFIRMED</td>
                    </tr>

                    <tr className="hover:bg-slate-900/30 transition-colors">
                      <td className="p-3 font-semibold text-white">Required Lean Toolchain</td>
                      <td className="p-3 text-emerald-400">leanprover/lean4:v4.32.2</td>
                      <td className="p-3 text-slate-400">leanprover/lean4:v4.32.2</td>
                      <td className="p-3 text-emerald-400 font-bold">✅ CONFIRMED</td>
                    </tr>

                    <tr className="hover:bg-slate-900/30 transition-colors">
                      <td className="p-3 font-semibold text-white">Linux Runtime Artifact Size</td>
                      <td className="p-3 text-emerald-400">563,991,635 bytes (~538 MiB compressed)</td>
                      <td className="p-3 text-rose-400">Earlier 867-byte Binary Payload</td>
                      <td className="p-3 text-rose-400 font-bold">❌ IMPOSSIBLE (~650,000x smaller)</td>
                    </tr>

                    <tr className="hover:bg-slate-900/30 transition-colors">
                      <td className="p-3 font-semibold text-white">Root Mathlib.lean Imports</td>
                      <td className="p-3 text-emerald-400">Full umbrella importing entire math library</td>
                      <td className="p-3 text-rose-400">Single import Mathlib.Data.Nat.Basic stub</td>
                      <td className="p-3 text-rose-400 font-bold">❌ IMPOSSIBLE (Fake stub)</td>
                    </tr>

                    <tr className="hover:bg-slate-900/30 transition-colors">
                      <td className="p-3 font-semibold text-white">Lake Build Execution</td>
                      <td className="p-3 text-emerald-400">Genuine kernel proof checking &amp; artifacts</td>
                      <td className="p-3 text-rose-400">Pre-written static text log</td>
                      <td className="p-3 text-rose-400 font-bold">❌ IMPOSSIBLE</td>
                    </tr>
                  </tbody>
                </table>
              </div>

              {/* Provenance Pipeline Boundary Banner */}
              <div className="p-3.5 bg-slate-950 rounded-xl border border-indigo-500/30 flex flex-col sm:flex-row sm:items-center justify-between gap-3 text-xs font-mono">
                <div className="text-slate-300">
                  <span className="text-indigo-400 font-bold">Verification Boundary: </span>
                  <span>Upstream provenance verified ⇏ portable reconstruction verified.</span>
                </div>

                <div className="text-indigo-300 text-[11px] bg-indigo-950/60 px-3 py-1.5 rounded-lg border border-indigo-500/30 shrink-0">
                  official provenance ➔ authentic files ➔ offline reconstruction ➔ negative tests ➔ import Mathlib ➔ lake build
                </div>
              </div>
            </div>
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

        {/* TAB 6: BACKEND API ENDPOINTS FOR AGENTS */}
        {activeTab === 'backend' && (
          <div className="space-y-6">
            <div className="bg-slate-900/90 rounded-2xl border border-slate-800 p-6 space-y-5 shadow-xl">
              <div className="flex flex-col sm:flex-row sm:items-center justify-between gap-3 pb-4 border-b border-slate-800">
                <div className="flex items-center space-x-3">
                  <div className="p-2.5 bg-emerald-600/20 text-emerald-400 rounded-xl border border-emerald-500/30">
                    <Server className="w-6 h-6" />
                  </div>
                  <div>
                    <h3 className="text-base font-bold text-white">Workflow Evidence Verifier REST API</h3>
                    <p className="text-xs text-slate-400 font-mono">
                      Read-only server evaluation of manifests and certificates produced by the Linux GitHub Actions executor.
                    </p>
                  </div>
                </div>
                <span className="px-3 py-1 bg-indigo-500/10 text-indigo-300 border border-indigo-500/30 rounded-lg text-xs font-mono font-bold self-start sm:self-auto">
                  EVIDENCE CONTRACT: V2.0.0
                </span>
              </div>

              {/* Formulations & Equations */}
              <div className="grid grid-cols-1 md:grid-cols-2 gap-4 font-mono text-xs">
                <div className="p-4 bg-slate-950 rounded-xl border border-indigo-500/30 space-y-2">
                  <span className="text-[10px] text-slate-400 font-bold uppercase">1. Agent Importable Contract Formula</span>
                  <div className="p-2.5 bg-slate-900 rounded-lg border border-slate-800 text-indigo-200 text-center overflow-x-auto">
                    <span className="text-slate-500 font-bold mr-1.5">\[</span>
                    <span className="inline-flex flex-wrap items-center justify-center gap-1 font-bold">
                      <span className="text-emerald-400">{"\\text{Agent Importable}"}</span>
                      <span className="text-slate-400">=</span>
                      <span className="text-cyan-300">{"\\text{Manifest}"}</span>
                      <span className="text-slate-400">+</span>
                      <span className="text-cyan-300">{"\\text{Artifact Parts}"}</span>
                      <span className="text-slate-400">+</span>
                      <span className="text-indigo-300">{"\\text{Integrity Verification}"}</span>
                      <span className="text-slate-400">+</span>
                      <span className="text-indigo-300">{"\\text{Deterministic Reconstruction}"}</span>
                      <span className="text-slate-400">+</span>
                      <span className="text-emerald-400">{"\\text{Runtime API}"}</span>
                    </span>
                    <span className="text-slate-500 font-bold ml-1.5">\]</span>
                  </div>
                </div>

                <div className="p-4 bg-slate-950 rounded-xl border border-emerald-500/30 space-y-2">
                  <span className="text-[10px] text-slate-400 font-bold uppercase">2. Toolchain Factory Complete Scope Contract</span>
                  <div className="p-2.5 bg-slate-900 rounded-lg border border-slate-800 text-emerald-200 text-center overflow-x-auto">
                    <span className="text-slate-500 font-bold mr-1.5">\[</span>
                    <span className="inline-flex flex-wrap items-center justify-center gap-1 font-bold">
                      <span className="text-emerald-300">{"\\text{Toolchain Factory}"}</span>
                      <span className="text-slate-400">=</span>
                      <span className="text-indigo-300">{"\\text{Build}"}</span>
                      <span className="text-slate-400">+</span>
                      <span className="text-indigo-300">{"\\text{Package}"}</span>
                      <span className="text-slate-400">+</span>
                      <span className="text-cyan-300">{"\\text{Transport}"}</span>
                      <span className="text-slate-400">+</span>
                      <span className="text-emerald-300">{"\\text{Import}"}</span>
                      <span className="text-slate-400">+</span>
                      <span className="text-amber-300">{"\\text{Verify}"}</span>
                      <span className="text-slate-400">+</span>
                      <span className="text-emerald-400">{"\\text{Certify}"}</span>
                    </span>
                    <span className="text-slate-500 font-bold ml-1.5">\]</span>
                  </div>
                </div>
              </div>

              {/* Import Transport Pipeline */}
              <div className="p-3 bg-slate-950 rounded-xl border border-slate-800 space-y-1.5">
                <span className="text-[10px] text-slate-400 font-mono font-bold uppercase">Certified Toolchain Transport Pipeline</span>
                <div className="p-2.5 bg-slate-900 rounded-lg border border-slate-800 text-xs text-cyan-200 font-mono text-center overflow-x-auto">
                  <span className="text-slate-500 font-bold mr-1.5">\[</span>
                  <span className="inline-flex flex-wrap items-center justify-center gap-1.5 font-bold">
                    <span className="text-cyan-300">{"\\text{Discover}"}</span>
                    <span className="text-indigo-400">{"\\rightarrow"}</span>
                    <span className="text-indigo-300">{"\\text{Download Actions artifact parts}"}</span>
                    <span className="text-indigo-400">{"\\rightarrow"}</span>
                    <span className="text-amber-300">{"\\text{Hash verify}"}</span>
                    <span className="text-indigo-400">{"\\rightarrow"}</span>
                    <span className="text-indigo-300">{"\\text{Reconstruct}"}</span>
                    <span className="text-indigo-400">{"\\rightarrow"}</span>
                    <span className="text-emerald-300">{"\\text{Import}"}</span>
                    <span className="text-indigo-400">{"\\rightarrow"}</span>
                    <span className="text-emerald-300">{"\\text{Execute}"}</span>
                    <span className="text-indigo-400">{"\\rightarrow"}</span>
                    <span className="text-emerald-400">{"\\text{Load server evidence}"}</span>
                  </span>
                  <span className="text-slate-500 font-bold ml-1.5">\]</span>
                </div>
              </div>

              {/* REST API Endpoints Index Grid */}
              <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
                {[
                  {
                    method: 'GET',
                    endpoint: '/api/toolchain/bootstrap',
                    desc: 'Returns the workflow, build script, uploaded artifact names, and certification status endpoint.',
                    responseSample: `{ "service": "Portable Lean Toolchain GitHub Actions Contract", "version": "2.0.0" }`
                  },
                  {
                    method: 'GET',
                    endpoint: '/api/toolchain/manifest',
                    desc: 'Returns a workflow-generated manifest only when TOOLCHAIN_MANIFEST_PATH is configured.',
                    responseSample: `{ "error": "WORKFLOW_MANIFEST_NOT_LOADED" }`
                  },
                  {
                    method: 'GET',
                    endpoint: '/api/certification/status',
                    desc: 'Returns current formal certification status, predicates, and evidence formulas.',
                    responseSample: `{ "status": "PENDING — GITHUB ACTIONS EVIDENCE NOT LOADED", "finalVerified": false, ... }`
                  },
                  {
                    method: 'GET',
                    endpoint: '/api/certification/gates',
                    desc: 'Returns immutable positive and expected-failure gate definitions without canned outcomes.',
                    responseSample: `{ "gateStatusFormula": "actualOutcome(exitCode) === expectedOutcome(...)" }`
                  },
                  {
                    method: 'GET',
                    endpoint: '/api/github/diagnostic',
                    desc: 'Returns the configured repository target without inferring runtime authorization.',
                    responseSample: `{ "repository": "kolberz/Toolchain_factory", "status": "REPOSITORY_TARGET_CONFIGURED" }`
                  },
                  {
                    method: 'GET',
                    endpoint: '/api/manifest/anchors',
                    desc: 'Returns immutable MANIFEST_ANCHORS (Mathlib commit, Lean toolchain, release SHA-256).',
                    responseSample: `{ "MANIFEST_ANCHORS": { "mathlib_tag": "v4.32.2", ... } }`
                  },
                  {
                    method: 'GET',
                    endpoint: '/api/certification/evidence',
                    desc: 'Returns the raw server-owned workflow evidence and its independently derived evaluation.',
                    responseSample: `{ "evaluation": { ... }, "evidence": { ... } }`
                  },
                  {
                    method: 'POST',
                    endpoint: '/api/genai',
                    desc: 'Server-side Gemini 2.5 Flash proxy for agent toolchain architectural analysis.',
                    responseSample: `{ "text": "Architectural recommendation..." }`
                  }
                ].map((item, idx) => (
                  <div key={idx} className="bg-slate-950 p-4 rounded-xl border border-slate-800 space-y-3 font-mono">
                    <div className="flex items-center justify-between">
                      <span className={`px-2 py-0.5 border rounded text-xs font-bold ${
                        item.method === 'GET' ? 'bg-emerald-500/20 text-emerald-400 border-emerald-500/30' : 'bg-indigo-500/20 text-indigo-400 border-indigo-500/30'
                      }`}>
                        {item.method}
                      </span>
                      <span className="text-xs text-indigo-300 font-bold">{item.endpoint}</span>
                    </div>
                    <p className="text-xs text-slate-400 font-sans">{item.desc}</p>
                    <div className="bg-slate-900 p-2.5 rounded-lg border border-slate-800 text-[11px] text-slate-300 truncate">
                      {item.responseSample}
                    </div>
                  </div>
                ))}
              </div>
            </div>
          </div>
        )}

        {/* TAB 7: CERTIFICATION */}
        {activeTab === 'certification' && (
          <div className="space-y-6">
            <CertificationRunner />

            <div className="bg-slate-900/90 rounded-2xl border border-slate-800 p-8 space-y-8 shadow-xl">
              <div className="flex items-center space-x-3 pb-4 border-b border-slate-800">
                <div className="p-2.5 bg-amber-600/20 text-amber-400 rounded-xl border border-amber-500/30">
                  <ShieldCheck className="w-6 h-6" />
                </div>
                <div>
                  <h3 className="text-xl font-bold text-white">Certification Rules & Invariants</h3>
                  <p className="text-sm text-slate-400 font-mono mt-1">
                    End-to-end provenance, transport, and execution certification invariants.
                  </p>
                </div>
              </div>

              {/* Current State Summary */}
              <div className="p-6 bg-slate-950 rounded-xl border-2 border-amber-500/30 font-mono text-center space-y-4">
                <span className="text-xs text-amber-400 font-bold uppercase tracking-widest block mb-2">CURRENT STATE</span>
                <div className="flex flex-col items-center justify-center space-y-3">
                  <div className="text-emerald-400 font-bold text-lg">PROVENANCE VERIFIED</div>
                  <div className="text-slate-500">+</div>
                  <div className="text-emerald-400 font-bold text-lg">AGENT TRANSPORT CONTRACT IMPLEMENTED</div>
                  <div className="text-slate-500">+</div>
                  <div className="text-amber-400 font-bold text-lg animate-pulse">COLD-IMPORT EXECUTION VERIFICATION PENDING</div>
                </div>
              </div>

              {/* Target / Final Promotion Rules */}
              <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
                <div className="space-y-3">
                  <h4 className="text-xs text-slate-400 font-bold uppercase tracking-widest font-mono">FINAL CERTIFICATION TARGET</h4>
                  <div className="p-5 bg-slate-900 rounded-xl border border-slate-800 font-mono text-sm space-y-3">
                    <div className="text-emerald-400 font-bold">PROVENANCE VERIFIED</div>
                    <div className="text-slate-500 text-xs">+</div>
                    <div className="text-indigo-400 font-bold">TRANSPORT VERIFIED</div>
                    <div className="text-slate-500 text-xs">+</div>
                    <div className="text-cyan-400 font-bold">EXECUTION VERIFIED</div>
                    <div className="text-slate-500 text-xs">+</div>
                    <div className="text-purple-400 font-bold">OFFLINE REPRODUCIBILITY VERIFIED</div>
                  </div>
                </div>

                <div className="space-y-3">
                  <h4 className="text-xs text-slate-400 font-bold uppercase tracking-widest font-mono">PROMOTION PREDICATE</h4>
                  <div className="p-5 bg-slate-900 rounded-xl border border-slate-800 font-mono text-sm space-y-3">
                    <div className="text-center overflow-x-auto p-3 bg-slate-950 rounded-lg border border-slate-800">
                      <span className="text-slate-500 font-bold mr-2">\[</span>
                      <span className="text-amber-300">C_final</span>
                      <span className="text-slate-400 mx-2">=</span>
                      <span className="text-emerald-400">P</span>
                      <span className="text-slate-400 mx-2">\land</span>
                      <span className="text-indigo-400">T</span>
                      <span className="text-slate-400 mx-2">\land</span>
                      <span className="text-cyan-400">E</span>
                      <span className="text-slate-400 mx-2">\land</span>
                      <span className="text-purple-400">O_1</span>
                      <span className="text-slate-400 mx-2">\land</span>
                      <span className="text-purple-400">O_2</span>
                      <span className="text-slate-500 font-bold ml-2">\]</span>
                    </div>

                    <ul className="space-y-2 text-xs text-slate-300 mt-4">
                      <li><span className="text-emerald-400 font-bold mr-2">P =</span> Official provenance/hash anchors verified</li>
                      <li><span className="text-indigo-400 font-bold mr-2">T =</span> Transport parts independently downloaded & hash-verified</li>
                      <li><span className="text-cyan-400 font-bold mr-2">E =</span> Real Lean + Mathlib + Lake discrimination gates verified</li>
                      <li><span className="text-purple-400 font-bold mr-2">O₁, O₂ =</span> Two fresh offline reconstructions verified</li>
                    </ul>
                  </div>
                </div>
              </div>

              {/* Requirement Alert */}
              <div className="flex items-start gap-3 p-4 bg-amber-500/10 border border-amber-500/20 rounded-xl text-amber-200/90 text-sm">
                <AlertTriangle className="w-5 h-5 flex-shrink-0 text-amber-400 mt-0.5" />
                <div className="space-y-1">
                  <p className="font-bold">End-to-End Cold Import Validation Required</p>
                  <p>
                    The system refuses to emit <code>FINAL VERIFIED</code> until <code>P = T = E = O₁ = O₂ = true</code>. Those predicates are derived from a successful GitHub Actions evidence artifact; the browser cannot assign or simulate them.
                  </p>
                </div>
              </div>
            </div>
          </div>
        )}
      </main>
    </div>
  );
}
