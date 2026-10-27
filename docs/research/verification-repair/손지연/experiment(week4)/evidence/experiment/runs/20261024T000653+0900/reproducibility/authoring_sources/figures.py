"""Standalone scientific plots from measured rows, never fabricated USD curves."""
import os
from pathlib import Path
from common import HERE,read,run_dir
os.environ['MPLCONFIGDIR']=str(HERE/'.matplotlib')
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

def main():
    run=run_dir();out=run/'figures';out.mkdir(exist_ok=True)
    summary=read(run/'analysis/summary.json')
    per_problem=read(run/'analysis/problem_summary.json')
    if any(s['completed'] for s in summary):
        fig,axes=plt.subplots(2,2,figsize=(10,7),layout='constrained')
        metrics=[('mean_token_reduction','Proof token reduction (%)'),('mean_heartbeat_reduction','Heartbeat reduction (%)'),
            ('mean_compatibility','Zero-shot compatibility (%)'),('mean_local_score','Post hoc local score')]
        for ax,(key,label) in zip(axes.flat,metrics):
            for i,s in enumerate(summary):
                if s[key] is None:continue
                ax.bar(i,s[key],color=f'C{i}',alpha=.45,width=.6)
                values=[p[key] for p in per_problem if p['family']=='P_A' and p['condition']==s['condition'] and p[key] is not None]
                offsets=[(j%5-2)*.035 for j in range(len(values))]
                ax.scatter([i+x for x in offsets],values,color=f'C{i}',s=16,alpha=.75)
                n=s['compatibility_measured'] if key in ('mean_compatibility','mean_local_score') else s['completed']
                ax.annotate(f'{s[key]:.1f}\nn={n}',(i,s[key]),xytext=(0,5),textcoords='offset points',ha='center',fontsize=8)
            ax.set_xticks(range(4),['A0','A1','A2','A3']);ax.set_ylabel(label);ax.axhline(0,color='.7',lw=.7)
            ax.margins(y=.2)
        fig.suptitle('P-A: 15 problems × 3 independent repeats per condition\nBars: history means; dots: problem means; original fallback included',fontsize=12)
        for ext in ('png','svg'):fig.savefig(out/f'performance_summary.{ext}',dpi=160)
        plt.close(fig)
    rows=read(run/'analysis/candidate_measurements.json')
    rows=[r for r in rows if r['origin']=='generated']
    if rows:
        fig,ax=plt.subplots(figsize=(8,5),layout='constrained')
        for condition,marker in zip(('A0','A1','A2','A3'),('o','s','^','D')):
            values=[r for r in rows if r['condition']==condition and r['compatibility'] is not None]
            if values:
                points=ax.scatter([r['token_reduction_pct'] for r in values],[r['heartbeat_reduction_pct'] for r in values],
                    c=[r['compatibility'] for r in values],vmin=0,vmax=100,cmap='viridis',marker=marker,alpha=.7,label=condition)
        ax.axhline(0,color='.75',lw=.8);ax.axvline(0,color='.75',lw=.8)
        ax.set(xlabel='Proof token reduction (%)',ylabel='Heartbeat reduction (%)',title='Generated valid candidates (holdout measured only)')
        if any(r['heartbeat_reduction_pct'] is not None and r['heartbeat_reduction_pct'] < -150 for r in rows):
            ax.set_yscale('symlog',linthresh=100)
            ax.set_ylabel('Heartbeat reduction (%)\nsymlog outside ±100%')
        ax.margins(x=.07,y=.15)
        handles,labels=ax.get_legend_handles_labels()
        if handles:ax.legend();fig.colorbar(points,ax=ax,label='Zero-shot compatibility (%)')
        for ext in ('png','svg'):fig.savefig(out/f'tradeoff.{ext}',dpi=160)
        plt.close(fig)
    policies=read(run/'analysis/selection_comparison.json')
    if policies:
        fig,axes=plt.subplots(2,2,figsize=(10,8),sharex=True,sharey=True,layout='constrained')
        labels=[('min_tokens','B1: minimum proof tokens'),('min_heartbeats','B2: minimum heartbeats'),
            ('max_compatibility','B3: maximum compatibility'),('max_local_score','B4: maximum local score')]
        points=None
        measured=[]
        for ax,(policy,title),marker in zip(axes.flat,labels,('o','s','^','D')):
            values=[r['measurement'] for r in policies if r['policy']==policy and r['available'] and r['measurement']['compatibility'] is not None]
            measured.extend(values)
            if values:
                points=ax.scatter([r['token_reduction_pct'] for r in values],[r['heartbeat_reduction_pct'] for r in values],
                    c=[r['compatibility'] for r in values],vmin=0,vmax=100,cmap='viridis',marker=marker,alpha=.55,s=35,edgecolors='.3',linewidths=.35)
            ax.axhline(0,color='.75',lw=.8);ax.axvline(0,color='.75',lw=.8)
            ax.set_title(title+f' (n={len(values)})',fontsize=11)
            ax.set_xlabel('Proof token reduction (%)');ax.set_ylabel('Heartbeat reduction (%)')
        if any(r['heartbeat_reduction_pct'] < -150 for r in measured):
            for ax in axes.flat:ax.set_yscale('symlog',linthresh=100);ax.set_ylabel('HB reduction (%)\nsymlog outside ±100%')
        for ax in axes.flat:ax.margins(x=.07,y=.15)
        if points is not None:fig.colorbar(points,ax=list(axes.flat),label='Zero-shot compatibility (%)',shrink=.85)
        fig.suptitle('Post hoc selection policies — same candidate set within each history',fontsize=13)
        for ext in ('png','svg'):fig.savefig(out/f'selection_tradeoff.{ext}',dpi=160)
        plt.close(fig)
    curve=read(run/'analysis/budget_curve.json')
    if curve:
        fig,ax=plt.subplots(figsize=(8,5),layout='constrained')
        for condition,color in zip(('A0','A1','A2','A3'),('C0','C1','C2','C3')):
            paths={r['history'] for r in curve if r['condition']==condition}
            for h in paths:
                values=[r for r in curve if r['history']==h]
                ax.step([r['model_tokens']/1000 for r in values],[r['search_score'] for r in values],where='post',alpha=.15,color=color)
            if paths:ax.plot([],[],color=color,label=condition)
        ax.set(xlabel='Cumulative model tokens (thousands; all calls)',ylabel='Available best base search score',
            title='Within-run anytime performance (subscription; USD unavailable)')
        ax.legend()
        for ext in ('png','svg'):fig.savefig(out/f'token_budget_curve.{ext}',dpi=160)
        plt.close(fig)
    values=read(run/'analysis/feedback_comparison.json')
    if any(r['completed'] for r in values):
        fig,ax=plt.subplots(figsize=(7,4),layout='constrained')
        labels=[r['condition']+'\n'+r['error_category'] for r in values]
        heights=[100*r['success_rate'] if r['success_rate'] is not None else 0 for r in values]
        bars=ax.bar(labels,heights,color=['C0','C0','C1','C1'])
        ax.set(ylabel='Verified (%)',ylim=(0,112),title='Repair success (completed histories only)')
        for bar,r in zip(bars,values):ax.text(bar.get_x()+bar.get_width()/2,bar.get_height()+2,f"{r['verified']}/{r['completed']}",ha='center')
        for ext in ('png','svg'):fig.savefig(out/f'feedback_success.{ext}',dpi=160)
        plt.close(fig)

if __name__=='__main__':main()
