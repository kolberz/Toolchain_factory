import React, { useCallback, useEffect, useState } from 'react';
import { AlertTriangle, Check, CheckCircle2, Copy, Download, RefreshCw, ShieldCheck, Terminal, XCircle } from 'lucide-react';

interface Predicate {
  name: string;
  value: boolean;
  state: 'VERIFIED' | 'FAILED' | 'PENDING';
  reasons: string[];
}

interface StatusResponse {
  status: string;
  formula: string;
  finalVerified: boolean;
  predicates: Record<'P' | 'T' | 'E' | 'O_1' | 'O_2' | 'R', Predicate>;
  evidenceSha256: string | null;
  evidenceSource: string;
  generatedAt: string | null;
  loadError?: string | null;
}

const predicateOrder: Array<'P' | 'T' | 'E' | 'O_1' | 'O_2' | 'R'> = ['P', 'T', 'E', 'O_1', 'O_2', 'R'];

export const CertificationRunner: React.FC = () => {
  const [status, setStatus] = useState<StatusResponse | null>(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [logs, setLogs] = useState<string[]>([]);
  const [copied, setCopied] = useState(false);

  const appendLog = useCallback((message: string) => {
    setLogs(previous => [...previous, `[${new Date().toLocaleTimeString()}] ${message}`]);
  }, []);

  const refresh = useCallback(async () => {
    setLoading(true);
    setError(null);
    appendLog('Requesting the server-derived certification verdict.');
    try {
      const response = await fetch('/api/certification/status', { cache: 'no-store' });
      const body = await response.json();
      if (!response.ok) throw new Error(body?.message || `Status request failed (${response.status}).`);
      setStatus(body);
      appendLog(body.finalVerified
        ? `FINAL VERIFIED from workflow evidence ${body.evidenceSha256}.`
        : `Not certified: ${body.status}. No predicate was assigned by this browser.`);
      if (body.loadError) appendLog(`Evidence load error: ${body.loadError}`);
    } catch (caught: any) {
      const message = caught?.message || 'Unable to load certification status.';
      setError(message);
      appendLog(`ERROR: ${message}`);
    } finally {
      setLoading(false);
    }
  }, [appendLog]);

  useEffect(() => { void refresh(); }, [refresh]);

  const copyLogs = async () => {
    await navigator.clipboard.writeText(logs.join('\n'));
    setCopied(true);
    window.setTimeout(() => setCopied(false), 1500);
  };

  return (
    <div className="space-y-6">
      <section className="bg-slate-900/90 rounded-2xl border border-slate-800 p-6 shadow-xl space-y-6">
        <div className="flex flex-col lg:flex-row lg:items-center justify-between gap-4 pb-6 border-b border-slate-800">
          <div className="flex items-center gap-3">
            <div className="p-3 bg-indigo-600/20 text-indigo-400 rounded-2xl border border-indigo-500/30">
              <ShieldCheck className="w-7 h-7" />
            </div>
            <div>
              <div className="flex items-center gap-2">
                <h2 className="text-xl font-bold text-white">Workflow Evidence Certification</h2>
                <span className="px-2.5 py-0.5 bg-cyan-500/10 text-cyan-300 border border-cyan-500/30 rounded-full text-[10px] font-mono font-bold">
                  SERVER-DERIVED
                </span>
              </div>
              <p className="text-xs text-slate-400 mt-1">
                This page reads evidence produced by the Linux GitHub Actions executor. It cannot run Lean or set certification predicates.
              </p>
            </div>
          </div>

          <div className={`p-4 rounded-xl border font-mono text-xs flex items-center gap-3 ${
            status?.finalVerified
              ? 'bg-emerald-950/80 border-emerald-500/50 text-emerald-300'
              : 'bg-slate-950 border-amber-500/30 text-amber-300'
          }`}>
            {status?.finalVerified
              ? <CheckCircle2 className="w-6 h-6 text-emerald-400" />
              : <AlertTriangle className="w-6 h-6 text-amber-400" />}
            <div>
              <div className="uppercase text-[10px] tracking-wider text-slate-400">Current verdict</div>
              <div className="text-sm font-bold">{status?.status || 'LOADING EVIDENCE'}</div>
              <div className="text-[10px] text-slate-500">{status?.generatedAt ? `Generated ${status.generatedAt}` : 'No successful workflow evidence loaded'}</div>
            </div>
          </div>
        </div>

        <div className="flex flex-col sm:flex-row gap-3 p-4 bg-slate-950 rounded-xl border border-slate-800">
          <button
            onClick={() => void refresh()}
            disabled={loading}
            className="px-4 py-2 bg-indigo-600 hover:bg-indigo-500 disabled:opacity-50 text-white text-xs font-semibold rounded-xl flex items-center justify-center gap-2"
          >
            <RefreshCw className={`w-4 h-4 ${loading ? 'animate-spin' : ''}`} />
            Refresh server evidence
          </button>
          <a
            href="/api/certification/evidence"
            target="_blank"
            rel="noreferrer"
            className="px-4 py-2 bg-slate-800 hover:bg-slate-700 text-slate-200 text-xs font-semibold rounded-xl flex items-center justify-center gap-2 border border-slate-700"
          >
            <Download className="w-4 h-4" />
            Open raw evidence
          </a>
          <div className="min-w-0 flex-1 text-[11px] font-mono text-slate-500 sm:text-right self-center truncate" title={status?.evidenceSource}>
            Source: {status?.evidenceSource || 'not loaded'}
          </div>
        </div>

        {error && <div className="p-3 bg-rose-950/40 border border-rose-500/30 rounded-xl text-xs text-rose-300">{error}</div>}

        <div className="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-6 gap-3">
          {predicateOrder.map(code => {
            const item = status?.predicates?.[code];
            return (
              <div key={code} className={`p-4 rounded-xl border ${
                item?.value ? 'bg-emerald-950/40 border-emerald-500/40' : item?.state === 'FAILED' ? 'bg-rose-950/20 border-rose-500/30' : 'bg-slate-950 border-slate-800'
              }`}>
                <div className="flex items-center justify-between mb-2">
                  <span className="text-xs font-mono font-bold text-white">{code.replace('_1', '₁').replace('_2', '₂')}</span>
                  {item?.value ? <CheckCircle2 className="w-4 h-4 text-emerald-400" /> : <XCircle className="w-4 h-4 text-slate-600" />}
                </div>
                <div className="text-[10px] font-bold tracking-wide text-slate-300">{item?.state || 'PENDING'}</div>
                <div className="text-[11px] text-slate-400 mt-1 leading-tight">{item?.name}</div>
                {item?.reasons?.map(reason => <div key={reason} className="text-[10px] text-rose-300 mt-2">{reason}</div>)}
              </div>
            );
          })}
        </div>

        <div className="p-4 bg-slate-950 rounded-xl border border-indigo-500/30 text-center font-mono text-xs">
          <span className={status?.finalVerified ? 'text-emerald-400 font-bold' : 'text-amber-400 font-bold'}>
            {status?.formula || 'C_final = P ∧ T ∧ E ∧ O₁ ∧ O₂ ∧ R = false'}
          </span>
          {status?.evidenceSha256 && <div className="mt-2 text-[10px] text-slate-500 break-all">Evidence SHA-256: {status.evidenceSha256}</div>}
        </div>
      </section>

      <section className="bg-slate-900/90 rounded-2xl border border-slate-800 p-5 space-y-3 shadow-xl">
        <div className="flex items-center justify-between pb-2 border-b border-slate-800">
          <div className="flex items-center gap-2">
            <Terminal className="w-4 h-4 text-emerald-400" />
            <h3 className="text-xs font-mono font-bold text-white uppercase tracking-wider">Evidence audit log</h3>
          </div>
          <button onClick={() => void copyLogs()} disabled={logs.length === 0} className="px-2.5 py-1 bg-slate-800 text-slate-200 text-xs rounded-lg flex items-center gap-1">
            {copied ? <Check className="w-3.5 h-3.5 text-emerald-400" /> : <Copy className="w-3.5 h-3.5" />}
            {copied ? 'Copied' : 'Copy'}
          </button>
        </div>
        <div className="bg-slate-950 rounded-xl p-4 h-44 overflow-y-auto font-mono text-xs border border-slate-800/80">
          {logs.map((line, index) => <div key={index} className={line.includes('ERROR') ? 'text-rose-400' : line.includes('FINAL VERIFIED') ? 'text-emerald-400' : 'text-slate-300'}>{line}</div>)}
        </div>
      </section>
    </div>
  );
};
