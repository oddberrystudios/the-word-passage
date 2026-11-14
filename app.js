/* The Word Passage — HTML5 client. Pure browser JS, no external libraries or services. */
(() => {
'use strict';
const data=window.WB_DATA, config=window.WB_CONFIG||{};
const $=id=>document.getElementById(id);
if(!data||!Array.isArray(data.levels)||data.levels.length!==5000){$('dataError').classList.remove('hidden');return;}
const alpha='ABCDEFGHIJKLMNOPQRSTUVWXYZ'.split('');
const accepted=new Map(),familiar=new Map();
for(const n of ['3','4','5']){accepted.set(Number(n),new Set(data.accepted[n]||[]));familiar.set(Number(n),new Set(data.familiar[n]||[]));}
const STORAGE='word_bridges_save_v1';
const defaultSettings={music:true,sfx:true,reducedMotion:false};
const saved=(()=>{try{return JSON.parse(localStorage.getItem(STORAGE)||'null')}catch{return null}})();
let settings={...defaultSettings,...(saved?.settings||{})};
const BANK_REV=data.bankRevision||'original';
const stableIds=new Map([...data.levels,...data.reserve].map(l=>[String(l.id),l]));
let recentPerformance=Array.isArray(saved?.recentPerformance)?saved.recentPerformance.slice(-12):[];
let lastScoredLevel=Number.isSafeInteger(saved?.lastScoredLevel)?saved.lastScoredLevel:0;
let adaptiveBlock=(saved?.bankRevision===BANK_REV&&saved?.adaptiveBlock&&Array.isArray(saved.adaptiveBlock.order))?saved.adaptiveBlock:null;
let currentStats={invalid:0,undo:0,hint:0,started:Date.now()};

let levelNumber=Number.isSafeInteger(saved?.level)&&saved.level>=1?saved.level:1;
// Old saves contain only the level number and current chain. Pin that exact
// unfinished puzzle across a bank upgrade, so refreshing won't switch targets.
let pinnedLevel=null;
if(saved?.bankRevision===BANK_REV&&saved?.pinnedLevelId){
 pinnedLevel=stableIds.get(String(saved.pinnedLevelId))||null;
}else if(saved?.bankRevision!==BANK_REV&&Array.isArray(saved?.chain)&&saved.chain.length){
 let oldId=levelNumber;
 if(levelNumber>5000){const n=levelNumber-5001,sz=5222,round=Math.floor(n/sz);oldId='r'+(((n%sz)*173+round*11)%sz+1);}
 const old=stableIds.get(String(oldId));
 if(old&&old.start===saved.chain[0])pinnedLevel=old;
}

let chain=[],freeHintUsed=false,selectedIndex=null,hintPosition=-1,strongHintWord='',scene='menu',dialogOpen=false,completeOpen=false;
let typedDraft='',mobileTyping=false,feedbackTimer=null;
// First-step guidance is persisted: Undo and reload must not replay onboarding.
let firstMoveLearned=!!saved?.firstMoveLearned||levelNumber>1||(saved?.level===1&&saved?.chain?.length>1);
// When a video is unavailable, clues progress from position to letter.
// A manual fallback NEVER enters a word automatically.
let fallbackHintWord='',fallbackHintStage=0;
let adFallbackActive=!!(saved?.level===levelNumber&&saved?.adFallbackActive);
let toastTimer=null,saveTimer=null,completionTimer=null,pausedForAd=false;
let solutionCache=null, lastAdAt=0;
let soundReady=false;

function getBlockStart(num){return num>=51&&num<=5000?51+10*Math.floor((num-51)/10):0;}
function difficultyMode(){
 const recent=recentPerformance.slice(-8);if(recent.length<6)return 'balanced';
 const struggling=recent.filter(p=>p.hint>0||p.invalid>=3||p.undo>=3||p.extra>=3||(p.activeMs>=110000&&p.activeMs<300000)).length;
 if(struggling>=4)return 'recovery';
 const effortless=recent.filter(p=>p.hint===0&&p.invalid<=1&&p.undo<=1&&p.extra<=1&&p.activeMs<40000).length;
 return effortless>=7?'confident':'balanced';
}
function ensureBlock(num){
 const start=getBlockStart(num);if(!start)return;
 if(adaptiveBlock?.start===start&&adaptiveBlock.order?.length===10)return;
 // Ten upcoming levels are a fixed, non-repeating set; adaptation ONLY
 // alters their order and never generates a new or unverified puzzle.
 const order=Array.from({length:10},(_,i)=>start-1+i);
 const mode=difficultyMode();
 if(mode==='recovery'){
  const sorted=order.slice().sort((a,b)=>data.levels[a].difficulty-data.levels[b].difficulty||a-b);
  order.splice(0,10,...[...sorted.slice(0,3),...sorted.slice(3).sort((a,b)=>a-b)]);
 }else if(mode==='confident'){
  const sorted=order.slice().sort((a,b)=>data.levels[a].difficulty-data.levels[b].difficulty||a-b);
  const hard=sorted.pop(),moderate=sorted.pop();
  order.splice(0,10,...[sorted[0],moderate,...sorted.slice(1),hard]);
 }
 adaptiveBlock={start,order,mode};
}
function levelAt(number){
 if(number===levelNumber&&pinnedLevel)return pinnedLevel;
 if(number<=5000){
  const start=getBlockStart(number);
  if(start&&adaptiveBlock?.start===start&&adaptiveBlock.order?.length===10)return data.levels[adaptiveBlock.order[number-start]];
  return data.levels[number-1];
 }
 // Every four-letter puzzle in the entire verified collection is part of
 // the endless cycle. The saved level number always resolves the same word pair.
 const order=data.endlessOrder||[];if(!order.length)return data.levels[(number-1)%5000];
 const n=number-5001,round=Math.floor(n/order.length),pos=(n%order.length+round*101)%order.length;
 const ix=order[pos];return ix<5000?data.levels[ix]:data.reserve[ix-5000];
}
function isMove(a,b){if(typeof a!=='string'||typeof b!=='string'||a.length!==b.length)return false;let d=0;for(let i=0;i<a.length;i++)if(a[i]!==b[i])d++;return d===1;}
function legalChain(c,level){if(!Array.isArray(c)||!c.length||c.length>500||c[0]!==level.start)return false;const bank=accepted.get(level.start.length);return c.every((word,i)=>typeof word==='string'&&bank.has(word)&&(i===0||isMove(c[i-1],word)));}
function loadLevelState(){const l=levelAt(levelNumber);chain= saved?.level===levelNumber&&legalChain(saved.chain,l)?saved.chain.slice():[l.start];freeHintUsed=!!(saved?.level===levelNumber&&saved?.freeHintUsed);selectedIndex=null;hintPosition=-1;strongHintWord='';solutionCache=null;typedDraft='';mobileTyping=false;}
ensureBlock(levelNumber);
loadLevelState();
function save(){try{localStorage.setItem(STORAGE,JSON.stringify({level:levelNumber,chain,freeHintUsed,firstMoveLearned,adFallbackActive,settings,bankRevision:BANK_REV,pinnedLevelId:pinnedLevel?.id||null,adaptiveBlock,recentPerformance,lastScoredLevel}))}catch{}}
function scoreCompletedLevel(){
 if(lastScoredLevel===levelNumber)return;
 const l=levelAt(levelNumber);
 currentStats.activeMs=Math.max(1,Math.min(300000,Date.now()-currentStats.started));
 recentPerformance.push({invalid:currentStats.invalid,undo:currentStats.undo,hint:currentStats.hint,
  extra:Math.max(0,chain.length-1-l.min_moves),activeMs:currentStats.activeMs});
 recentPerformance=recentPerformance.slice(-12);
 lastScoredLevel=levelNumber;
}

function setSettings(next){settings={...settings,...next};document.body.classList.toggle('reduced-motion',!!settings.reducedMotion);save();}
setSettings(settings);
function toast(message){const node=$('toast');node.textContent=message;node.classList.add('visible');clearTimeout(toastTimer);toastTimer=setTimeout(()=>node.classList.remove('visible'),2200);}
function hide(node){node.classList.add('hidden')}
function show(node){node.classList.remove('hidden')}
function openScreen(which){scene=which;document.body.dataset.scene=which;$('menuScreen').classList.toggle('hidden',which!=='menu');$('gameScreen').classList.toggle('hidden',which!=='game');if(which==='game')render();if(soundReady) sound.applySettings();}

class Sound {
  constructor(){
    this.ctx=null; this.master=null; this.lastSelect=0; this.unlocked=false; this.music=new Audio('assets/river-theme.mp3');
    this.music.loop=true; this.music.preload='auto'; this.music.volume=.24;
  }
  unlock(){
    try {
      this.ctx??=new (window.AudioContext||window.webkitAudioContext)();
      if(!this.master){this.master=this.ctx.createGain();this.master.gain.value=.85;this.master.connect(this.ctx.destination)}
      if(this.ctx.state==='suspended'&&!pausedForAd&&!document.hidden)this.ctx.resume().catch(()=>{});
      this.unlocked=true;
    }catch{}
    this.applySettings();
  }
  applySettings(){
    const shouldPlay=this.unlocked&&settings.music&&!pausedForAd&&!document.hidden;
    this.music.volume=scene==='menu'?.20:.26;
    if(shouldPlay&&this.music.paused)this.music.play().catch(()=>{});
    if(!shouldPlay&&!this.music.paused)this.music.pause();
  }
  tone(freq,duration=.17,vol=.06,delay=0,kind='mallet'){
    if(!this.ctx||this.ctx.state!=='running'||!this.master)return;
    const ctx=this.ctx, start=ctx.currentTime+delay;
    const g=ctx.createGain(),filter=ctx.createBiquadFilter();
    filter.type='lowpass';filter.frequency.setValueAtTime(kind==='soft'?1400:kind==='bell'?3400:2200,start);
    filter.Q.value=.4;g.connect(filter).connect(this.master);
    const attack=kind==='soft'?.030:.008;
    g.gain.setValueAtTime(.0001,start);
    g.gain.exponentialRampToValueAtTime(Math.max(.001,vol),start+attack);
    g.gain.exponentialRampToValueAtTime(.0001,start+duration);
    const partials=kind==='bell'?[[1,1],[2.01,.28],[3,.1]]:kind==='soft'?[[1,1],[2,.15]]:[[1,1],[2,.38],[3,.11]];
    for(const [mult,level] of partials){
      const o=ctx.createOscillator(),sg=ctx.createGain();o.type='sine';o.frequency.setValueAtTime(freq*mult,start);
      sg.gain.value=level;o.connect(sg).connect(g);o.start(start);o.stop(start+duration+.02);
      o.onended=()=>{try{o.disconnect();sg.disconnect()}catch{}};
    }
    const cleanup=()=>{try{g.disconnect();filter.disconnect()}catch{}};
    setTimeout(cleanup,Math.ceil((duration+delay+.08)*1000));
  }
  effect(kind){
    if(!settings.sfx||pausedForAd)return;
    this.unlock();
    const now=Date.now();
    if(kind==='select'){
      if(now-this.lastSelect<70)return;this.lastSelect=now;
      this.tone(620,.075,.013,0,'mallet');return;
    }
    if(kind==='valid'){
      this.tone(466.16,.21,.055,0,'mallet');
      this.tone(622.25,.29,.044,.074,'bell');return;
    }
    if(kind==='invalid'){
      this.tone(220,.13,.035,0,'soft');this.tone(185,.14,.024,.075,'soft');return;
    }
    if(kind==='undo'){
      this.tone(493.88,.15,.033,0,'soft');this.tone(392,.19,.027,.052,'soft');return;
    }
    if(kind==='hint'){
      this.tone(659.25,.32,.042,0,'bell');this.tone(830.61,.36,.032,.105,'bell');
      this.tone(987.77,.42,.025,.22,'bell');return;
    }
    if(kind==='win'){
      this.music.volume=.13;
      [523.25,659.25,783.99,1046.50].forEach((n,i)=>this.tone(n,.48,.048,i*.105,'bell'));
      this.tone(523.25,1.0,.027,.4,'soft');
      setTimeout(()=>this.applySettings(),1300);
    }
  }
  pause(){this.music.pause();if(this.ctx?.state==='running')this.ctx.suspend().catch(()=>{});}
  resume(){if(!this.unlocked||pausedForAd||document.hidden)return;
    if(this.ctx?.state==='suspended')this.ctx.resume().catch(()=>{});
    this.applySettings();
  }
}
const sound=new Sound(); soundReady=true;

// Games are fully playable offline. Ads initialize ONLY with an assigned GD game ID.
const ads={ready:false,pending:null,load(){if(!config.enableAds||!config.gdGameId)return;window.GD_OPTIONS={gameId:config.gdGameId,onEvent:event=>{switch(event?.name){case'SDK_GAME_PAUSE':pausedForAd=true;sound.pause();break;case'SDK_GAME_START':pausedForAd=false;sound.resume();break;case'SDK_REWARDED_WATCH_COMPLETE':this.pending?.(true);break;case'SDK_REWARDED_WATCH_FAILED':case'SDK_REWARDED_WATCH_ABORTED':this.pending?.(false);break;}}};const script=document.createElement('script');script.src='https://html5.api.gamedistribution.com/main.min.js';script.async=true;script.onload=()=>{this.ready=!!window.gdsdk;renderHintButton()};script.onerror=()=>{this.ready=false};document.head.appendChild(script);},interstitial(force=false){if(!this.ready||typeof window.gdsdk?.showAd!=='function')return;if(!force&&Date.now()-lastAdAt<60000)return;lastAdAt=Date.now();try{window.gdsdk.showAd()}catch(e){console.warn('GameDistribution interstitial unavailable',e)}},rewarded(){if(!this.ready||typeof window.gdsdk?.showAd!=='function')return Promise.resolve(false);return new Promise(resolve=>{let done=false;const finish=ok=>{if(done)return;done=true;clearTimeout(timer);this.pending=null;resolve(ok)};const timer=setTimeout(()=>finish(false),25000);this.pending=finish;try{window.gdsdk.showAd('rewarded')}catch{finish(false)}})}};
ads.load();

function neighbors(word,bank){const found=[];for(let i=0;i<word.length;i++){for(let code=97;code<=122;code++){const next=word.substring(0,i)+String.fromCharCode(code)+word.substring(i+1);if(next!==word&&bank.has(next))found.push(next);}}return found;}
function distanceToTarget(target,bank){const queue=[target],distance=new Map([[target,0]]);for(let i=0;i<queue.length;i++){const w=queue[i];for(const n of neighbors(w,bank))if(!distance.has(n)){distance.set(n,distance.get(w)+1);queue.push(n);}}return distance;}
function friendlyNext(current,target){
 const level=levelAt(levelNumber), bank=familiar.get(current.length), valid=accepted.get(current.length);
 // Prefer the carefully reviewed path when the player is still on it.
 const approved=level.hint_path||[]; const at=approved.indexOf(current);
 if(at>=0&&at+1<approved.length){
  const next=approved[at+1];
  if(bank.has(next)&&valid.has(next)&&isMove(current,next)&&!chain.slice(0,-1).includes(next))return {type:'word',word:next};
 }
 if(!solutionCache||solutionCache.target!==target)solutionCache={target,dist:distanceToTarget(target,bank)};
 const dist=solutionCache.dist;
 if(dist.has(current)){
  const d=dist.get(current);
  const opts=neighbors(current,bank).filter(w=>dist.has(w)&&dist.get(w)<d&&valid.has(w));
  opts.sort((a,b)=>{
    const repeatA=chain.includes(a)?1:0,repeatB=chain.includes(b)?1:0;
    if(repeatA!==repeatB)return repeatA-repeatB;
    const da=dist.get(a),db=dist.get(b);if(da!==db)return da-db;
    const targetMatch=w=>[...w].filter((c,i)=>c===target[i]).length;
    return targetMatch(b)-targetMatch(a)||a.localeCompare(b);
  });
  if(opts.length)return {type:'word',word:opts[0]};
 }
 // If off the familiar network, allow one safe step back onto it.
 const returning=neighbors(current,valid).filter(w=>bank.has(w)&&dist.has(w)&&!chain.includes(w));
 returning.sort((a,b)=>dist.get(a)-dist.get(b)||a.localeCompare(b));
 if(returning.length)return {type:'word',word:returning[0]};
 return {type:chain.length>1?'undo':'restart'};
}
function changedIndex(a,b){for(let i=0;i<a.length;i++)if(a[i]!==b[i])return i;return -1;}
function ordinal(i){return ['first','second','third','fourth','fifth'][i]||'selected';}
function renderHintButton(){
 const video=freeHintUsed&&ads.ready&&!adFallbackActive;
 $('hintVideo').classList.toggle('hidden',!video);
 $('hintButton').title=freeHintUsed?(video?'Watch a video to complete one step':'Guided clues — make the next move yourself'):'First guided letter change is free';
}
function renderFirstMoveTip(){
 const visible=levelNumber===1&&!firstMoveLearned&&chain.length===1&&!mobileTyping&&!typedDraft&&!completeOpen&&$('hintBanner').classList.contains('hidden');
 $('firstMoveTip').classList.toggle('hidden',!visible);
 if(visible)$('firstMoveTipText').textContent=selectedIndex===null?'Tap a letter, then choose its replacement.':'Now choose a letter below.';
}
function clearFeedback(){clearTimeout(feedbackTimer);$('feedbackLine').textContent='';$('feedbackLine').classList.remove('error','success');}
function feedback(message,type='error'){const el=$('feedbackLine');el.textContent=message;el.classList.toggle('error',type==='error');el.classList.toggle('success',type==='success');clearTimeout(feedbackTimer);feedbackTimer=setTimeout(()=>clearFeedback(),2400);}
function renderTypingMode(){
 $('typeModeToggle').setAttribute('aria-pressed',String(mobileTyping));$('typeModeLabel').textContent=mobileTyping?'A–Z':'TYPE';
 $('typeModeToggle').title=mobileTyping?'Show alphabet board':'Type the next word';
 $('typeModeToggle').setAttribute('aria-label',mobileTyping?'Show alphabet board':'Type the next word');
 $('directEntry').classList.toggle('hidden',!mobileTyping);$('alphabetBlock').classList.toggle('hidden',mobileTyping);
 $('controlsPanel').classList.toggle('typing-mode',mobileTyping);
 renderFirstMoveTip();
 document.body.classList.toggle('typing-active',mobileTyping);
 $('wordInput').maxLength=chain.at(-1).length;
 $('wordInput').placeholder=chain.at(-1).length+' LETTERS';
 if(mobileTyping&&$('wordInput').value.toLowerCase()!==typedDraft)$('wordInput').value=typedDraft.toUpperCase();
}
function render(){const l=levelAt(levelNumber);$('levelChip').textContent='LEVEL '+levelNumber.toLocaleString('en-US');$('startWord').textContent=l.start.toUpperCase();$('targetWord').textContent=l.target.toUpperCase();$('targetPanelWord').textContent=l.target.toUpperCase();$('movesPill').textContent=(chain.length-1)+' '+(chain.length===2?'move':'moves');renderPath();renderTiles();renderAlpha();renderTypingMode();renderHintButton();renderFirstMoveTip();$('undoButton').disabled=chain.length<=1&&!typedDraft;}
function wordChip(word,kind,step){
 const chip=document.createElement('div');chip.className='path-stone '+kind;
 if(kind==='empty'){
  chip.setAttribute('aria-label','Empty word step '+step);chip.setAttribute('role','listitem');
  for(let i=0;i<word.length;i++){const s=document.createElement('span');s.className='path-slot';chip.appendChild(s)}
 }else{
  chip.setAttribute('role','listitem');chip.setAttribute('aria-label',(kind==='goal'||kind==='reached'?'Target word ':kind==='active'?'Current word ':'Completed word ')+word);
  chip.appendChild(document.createTextNode(word.toUpperCase()));
  if(kind==='complete'||kind==='reached'){const c=document.createElement('span');c.className='path-check';c.textContent='✓';chip.appendChild(c)}
 }
 return chip;
}
function renderPath(){
 const track=$('pathTrack');track.replaceChildren();const level=levelAt(levelNumber),total=Number(level.min_moves)||level.hint_path?.length-1||3;
 const solved=chain.at(-1)===level.target;
 const addConnector=()=>{const con=document.createElement('div');con.className='path-connector';con.setAttribute('aria-hidden','true');track.appendChild(con)};
 for(let i=0;i<chain.length;i++){
  if(i>0)addConnector();
  const isLast=i===chain.length-1;
  track.appendChild(wordChip(chain[i],isLast?(solved?'reached':'active'):'complete',i+1));
 }
 // The goal is a reserved final slot, not an additional word after completion.
 // Reaching it fills that slot in place, so the target is never duplicated.
 if(!solved){
  const missing=Math.max(0,total-chain.length);
  for(let i=0;i<missing;i++){addConnector();track.appendChild(wordChip(level.start,'empty',chain.length+i+1));}
  addConnector();track.appendChild(wordChip(level.target,'goal',Math.max(total+1,chain.length+1)));
 }
 requestAnimationFrame(()=>{const sc=$('pathScroll');const active=track.querySelector('.path-stone.active, .path-stone.reached');if(!active)return;const desired=Math.max(0,active.offsetTop-sc.clientHeight*.38);sc.scrollTop=desired;});
}
function renderTiles(){
 const cur=chain.at(-1),root=$('currentTiles');root.replaceChildren();const drafting=typedDraft.length>0;
 for(let i=0;i<cur.length;i++){
  const b=document.createElement('button');b.type='button';
  b.className='current-tile'+(i===selectedIndex&&!drafting?' selected':'')+(i===hintPosition&&!drafting?' hint-tile':'')+(drafting?' draft-tile':'')+(drafting&&i>=typedDraft.length?' draft-empty':'');
  b.textContent=drafting?(typedDraft[i]?.toUpperCase()||'·'):cur[i].toUpperCase();
  b.setAttribute('aria-label',drafting?'Typed word letter '+(i+1):`Change letter ${i+1}, currently ${cur[i].toUpperCase()}`);
  b.dataset.index=i;b.addEventListener('click',()=>{
   if(completeOpen||dialogOpen)return;
   if(drafting){typedDraft='';if(mobileTyping)$('wordInput').value='';}
   mobileTyping=false;$('wordInput').blur();clearFeedback();selectedIndex=i;sound.effect('select');renderTiles();renderAlpha();renderTypingMode();
  });root.appendChild(b);
 }
 if(drafting){$('feedbackLine').textContent=typedDraft.length===cur.length?'PRESS ENTER TO CONFIRM':'TYPE NEXT WORD';$('feedbackLine').classList.remove('error','success');}
 else if(!mobileTyping&&!$('feedbackLine').classList.contains('error')&&!$('feedbackLine').classList.contains('success')){$('feedbackLine').textContent='';}
 renderFirstMoveTip();
}
function renderAlpha(){
 const root=$('alphabetGrid');root.replaceChildren();const cur=chain.at(-1);
 // Guide the tap order quietly, without an extra floating instruction.
 const label=$('alphabetBlock').querySelector('.alphabet-label');
 if(label)label.textContent=selectedIndex===null?'TAP A WORD LETTER':'CHOOSE REPLACEMENT';
 $('alphabetBlock').classList.toggle('letter-ready',selectedIndex!==null);
 alpha.forEach(letter=>{
  const b=document.createElement('button');b.type='button';
  const hintMatch=strongHintWord&&hintPosition===selectedIndex&&strongHintWord[hintPosition]===letter.toLowerCase();
  b.className='letter-btn'+(selectedIndex!==null&&!strongHintWord&&cur[selectedIndex]===letter.toLowerCase()?' selected-letter':'')+(hintMatch?' hint-answer':'');
  b.textContent=letter;
  b.setAttribute('aria-label','Replace selected letter with '+letter+(hintMatch?' - suggested move':''));
  b.addEventListener('click',()=>chooseLetter(letter.toLowerCase()));root.appendChild(b);
 });
}
function animateBadTile(){const index=selectedIndex!==null?selectedIndex:0;const tile=$('currentTiles').children[index];tile?.classList.add('invalid');setTimeout(()=>tile?.classList.remove('invalid'),360)}
function clearDraft(){typedDraft='';if($('wordInput'))$('wordInput').value='';}
function commitWord(next){
 const current=chain.at(-1),words=accepted.get(current.length);
 if(!isMove(current,next)){currentStats.invalid++;sound.effect('invalid');animateBadTile();feedback('CHANGE ONE LETTER');return false;}
 if(!words?.has(next)){currentStats.invalid++;sound.effect('invalid');animateBadTile();feedback('NOT A WORD');return false;}
 if(chain.includes(next)){
  const idx=chain.lastIndexOf(next); chain=chain.slice(0,idx+1);fallbackHintWord='';fallbackHintStage=0;selectedIndex=null;hintPosition=-1;strongHintWord='';hide($('hintBanner'));clearDraft();mobileTyping=false;$('wordInput').blur();clearFeedback();sound.effect('undo');save();render();return true;
 }
 $('toast').classList.remove('visible');clearTimeout(toastTimer);
 
 chain.push(next);if(levelNumber===1&&!firstMoveLearned)firstMoveLearned=true;
 fallbackHintWord='';fallbackHintStage=0;selectedIndex=null;hintPosition=-1;strongHintWord='';hide($('hintBanner'));clearDraft();mobileTyping=false;$('wordInput').blur();clearFeedback();sound.effect('valid');save();
 if(next===levelAt(levelNumber).target){sound.effect('win');render();clearTimeout(completionTimer);completionTimer=setTimeout(()=>completeLevel(),settings.reducedMotion?50:410);}else render();
 return true;
}
function chooseLetter(letter){
 if(scene!=='game'||completeOpen||dialogOpen||pausedForAd)return;
 if(selectedIndex===null){feedback('SELECT A LETTER ABOVE');return;}
 const current=chain.at(-1);if(current[selectedIndex]===letter){feedback('CHOOSE A DIFFERENT LETTER');return;}
 commitWord(current.slice(0,selectedIndex)+letter+current.slice(selectedIndex+1));
}
function confirmTyped(){
 if(scene!=='game'||completeOpen||dialogOpen||pausedForAd)return false;
 const next=typedDraft.trim().toLowerCase(),cur=chain.at(-1);
 if(next.length!==cur.length){feedback('ENTER '+cur.length+' LETTERS');sound.effect('invalid');return false;}
 const ok=commitWord(next);
 if(!ok&&mobileTyping)$('wordInput').focus();
 return ok;
}
function toggleTyping(){
 if(scene!=='game'||dialogOpen||completeOpen)return;
 mobileTyping=!mobileTyping;if(!mobileTyping)$('wordInput').blur();clearDraft();clearFeedback();selectedIndex=null;
 renderTiles();renderAlpha();renderTypingMode();
 if(mobileTyping){$('wordInput').value='';$('wordInput').focus();}

}
function undo(){if(typedDraft){clearDraft();clearFeedback();render();return;}if(chain.length<=1)return;currentStats.undo++;chain.pop();fallbackHintWord='';fallbackHintStage=0;selectedIndex=null;hintPosition=-1;strongHintWord='';hide($('hintBanner'));clearFeedback();sound.effect('undo');save();render();}
function hintText(text){$('hintBanner').textContent=text;show($('hintBanner'));renderFirstMoveTip();}
async function requestHint(){
 if(scene!=='game'||dialogOpen||completeOpen||pausedForAd)return;
 if(typedDraft||mobileTyping){clearDraft();mobileTyping=false;$('wordInput').blur();clearFeedback();renderTypingMode();renderTiles();}
 const current=chain.at(-1),target=levelAt(levelNumber).target;
 if(current===target)return;
 const hint=friendlyNext(current,target);
 if(hint.type==='undo'){
  hintText('Try Undo to return to a familiar word.');
  $('undoButton').classList.add('hint-undo');setTimeout(()=>$('undoButton').classList.remove('hint-undo'),1750);
  sound.effect('hint');return;
 }
 if(hint.type==='restart'){
  hintText('Try restarting this level.');sound.effect('hint');return;
 }
 const index=changedIndex(current,hint.word);
 if(index<0||!isMove(current,hint.word)||!accepted.get(current.length).has(hint.word))return;
 if(!freeHintUsed){
  currentStats.hint++;freeHintUsed=true;hintPosition=index;strongHintWord=hint.word;
  selectedIndex=index;fallbackHintWord=current;fallbackHintStage=2;
  hintText('Change '+current[index].toUpperCase()+' to '+hint.word[index].toUpperCase());
  sound.effect('hint');save();renderTiles();renderAlpha();renderHintButton();return;
 }
 // A watched rewarded video may complete exactly one valid move.
 // If video playback fails, or no SDK is configured, provide manual guidance
 // in two steps instead of auto-solving the puzzle without a reward.
 if(ads.ready&&!adFallbackActive){
  $('hintButton').disabled=true;
  let rewarded=false;
  try{rewarded=await ads.rewarded()}finally{$('hintButton').disabled=false;}
  if(scene!=='game'||completeOpen||dialogOpen)return;
  if(rewarded){
   const fresh=friendlyNext(chain.at(-1),levelAt(levelNumber).target);
   if(fresh.type==='word'&&isMove(chain.at(-1),fresh.word)){
    currentStats.hint++;sound.effect('hint');commitWord(fresh.word);
   }
   return;
  }
  // Don't trap players behind a broken or cancelled video. No free move.
  adFallbackActive=true;renderHintButton();save();
 }
 const fresh=friendlyNext(chain.at(-1),levelAt(levelNumber).target);
 if(fresh.type!=='word'||!isMove(chain.at(-1),fresh.word))return;
 const word=chain.at(-1),position=changedIndex(word,fresh.word);
 if(position<0)return;
 if(fallbackHintWord!==word){fallbackHintWord=word;fallbackHintStage=0;}
 fallbackHintStage=Math.min(2,fallbackHintStage+1);
 currentStats.hint++;
 hintPosition=position;
 if(fallbackHintStage===1){
  selectedIndex=null;strongHintWord='';
  hintText('Try changing the '+ordinal(position)+' letter.');
 }else{
  selectedIndex=position;strongHintWord=fresh.word;
  hintText('Change '+word[position].toUpperCase()+' to '+fresh.word[position].toUpperCase()+'.');
 }
 sound.effect('hint');save();renderTiles();renderAlpha();renderHintButton();
}
function completeLevel(){if(completeOpen||scene!=='game')return;
 scoreCompletedLevel();
 $('toast').classList.remove('visible');clearTimeout(toastTimer);completeOpen=true;const l=levelAt(levelNumber);const n=chain.length-1;$('completeLevelNum').textContent='LEVEL '+levelNumber.toLocaleString('en-US');const div=$('completeChain');div.replaceChildren();let shown=chain.length<=6?chain:chain.slice(-6);for(const [i,w] of shown.entries()){if(i){const arrow=document.createElement('i');arrow.textContent='›';arrow.setAttribute('aria-hidden','true');div.appendChild(arrow)}const s=document.createElement('span');s.textContent=w.toUpperCase();div.appendChild(s);}if(chain.length>6){const small=document.createElement('small');small.textContent='+'+(chain.length-6)+' earlier words';div.prepend(small)}$('completeMoves').textContent=n+' '+(n===1?'move':'moves');show($('completionBackdrop'));save();}
function nextLevel(){completeOpen=false;clearDraft();mobileTyping=false;document.body.classList.remove('typing-active');clearFeedback();hide($('completionBackdrop'));pinnedLevel=null;levelNumber++;ensureBlock(levelNumber);currentStats={invalid:0,undo:0,hint:0,started:Date.now()};const l=levelAt(levelNumber);chain=[l.start];freeHintUsed=false;fallbackHintWord='';fallbackHintStage=0;adFallbackActive=false;selectedIndex=null;hintPosition=-1;strongHintWord='';solutionCache=null;hide($('hintBanner'));save();openScreen('game');if(levelNumber>1&&levelNumber%4===1)ads.interstitial();}
function startGame(){sound.unlock();currentStats.started=Date.now();clearDraft();mobileTyping=false;clearFeedback();dialogOpen=false;hide($('dialogBackdrop'));hide($('completionBackdrop'));completeOpen=false;openScreen('game');ads.interstitial(true);if(chain.at(-1)===levelAt(levelNumber).target)completeLevel();}
function goHome(){clearTimeout(completionTimer);clearDraft();mobileTyping=false;$('wordInput').blur();clearFeedback();scene='menu';completeOpen=false;hide($('completionBackdrop'));hide($('dialogBackdrop'));dialogOpen=false;save();openScreen('menu');}

// Three self-contained How to Play scenes. Nothing here changes live puzzle data.
let helpStep=0, helpInputMode='tap', demoWord='card', demoSelected=-1, demoSolved=false;
let demoPath=['cold','cord'], demoHintIndex=-1, helpAnimNonce=0;
const guideTitles=['Reach the target','Make your move','Keep your path going'];
const guideIcon=(name)=>({
 refresh:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.3" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 7v5h-5"/><path d="M20 12a8 8 0 1 0-2.4 5.7"/></svg>',
 tap:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M9 11V5a2 2 0 0 1 4 0v7l1.5-1a2 2 0 0 1 2.5 1l3 4a4 4 0 0 1-4 6H11a6 6 0 0 1-4.6-2.1L3 16.3a2 2 0 0 1 2.9-2.8L9 16V11"/></svg>',
 keyboard:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="2" y="5" width="20" height="14" rx="2"/><path d="M6 9h.01M10 9h.01M14 9h.01M18 9h.01M6 12h.01M10 12h.01M14 12h.01M18 12h.01M7 16h10"/></svg>',
 undo:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M9 7 4 12l5 5M4 12h10a6 6 0 0 1 0 12"/></svg>',
 hint:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M9 18h6M10 21h4M8 15c-1.8-1.5-2.8-3.2-2.8-5A6.8 6.8 0 0 1 12 3.4 6.8 6.8 0 0 1 18.8 10c0 1.8-1 3.5-2.8 5-.8.7-1 1.3-1 2H9c0-.7-.2-1.3-1-2Z"/></svg>'
})[name]||'';
function guideResetPractice(){demoWord='card';demoSelected=-1;demoSolved=false;}
function guideResetTools(){demoPath=['cold','cord'];demoHintIndex=-1;}
function guideFrame(){return `<div class="wb-guide" id="wbGuide">
  <header class="wb-guide-header"><h2 id="dialogTitle">How to Play</h2><div class="wb-guide-steps" id="guideSteps" aria-label="Tutorial progress"></div></header>
  <div id="guideScene" class="wb-guide-content" aria-live="polite"></div>
  <footer class="wb-guide-footer"><button type="button" id="guideBack" class="wb-guide-back">Back</button><button type="button" id="guideNext" class="wb-guide-next">Next <span aria-hidden="true">→</span></button></footer>
 </div>`;}
function guideTileRow(word,{focus=-1,changed=-1,animate=false,goal=false}={}){
 return `<div class="wb-demo-letters ${animate?'wb-demo-enter':''} ${goal?'wb-demo-goal':''}">${[...word.toUpperCase()].map((c,i)=>`<span class="wb-demo-tile ${i===focus?'wb-demo-tile-focus':''} ${i===changed?'wb-demo-tile-change':''}">${c}</span>`).join('')}</div>`;
}
function guideProgress(){const root=$('guideSteps');if(!root)return;root.innerHTML=guideTitles.map((title,i)=>`<button type="button" class="wb-guide-step ${i===helpStep?'active':''} ${i<helpStep?'visited':''}" data-guide-page="${i}" aria-label="Page ${i+1}: ${title}" aria-current="${helpStep===i?'step':'false'}"></button>`).join('');}
function guideSceneGoal(){const words=['cat','cot','dot','dog'];return `<div class="wb-guide-scene wb-guide-goal-scene">
 <div class="wb-guide-copy"><div class="wb-guide-kicker">THE GOAL</div><h3>Reach the target</h3><p>Change <b>one letter</b> at a time. Each new word must be real.</p><div class="wb-guide-rulechips"><span>Same word length</span><span>One change per step</span></div></div>
 <div class="wb-showcase wb-route-showcase" aria-label="Example word path CAT, COT, DOT, DOG">
 <div class="wb-showcase-top"><span class="wb-showcase-label">CAT <span aria-hidden="true">→</span> DOG</span><button type="button" class="wb-guide-iconbtn" data-guide-replay aria-label="Replay example">${guideIcon('refresh')}</button></div>
 <div class="wb-guide-ladder">${words.map((word,i)=>`<div class="wb-ladder-row" style="--order:${i};--dur:${settings.reducedMotion?0:1}s"><div class="wb-ladder-card ${i===3?'wb-ladder-goal':''}">${[...word.toUpperCase()].map((char,j)=>`<span class="${i>0&&char!==words[i-1].toUpperCase()[j]?'wb-letter-updated':''}">${char}</span>`).join('')}</div>${i<3?'<span class="wb-ladder-connector" aria-hidden="true">↓</span>':''}</div>`).join('')}</div></div>
 </div>`;}
function guidePracticeTiles(){return `<div class="wb-guide-wordtiles" role="group" aria-label="Practice current word ${demoWord.toUpperCase()}">${[...demoWord.toUpperCase()].map((c,i)=>`<button type="button" class="wb-practice-tile ${i===demoSelected?'chosen':''} ${demoSolved?'solved':''} ${i===0&&!demoSolved&&demoSelected<0?'guided':''}" data-guide-pos="${i}" aria-label="Select ${c}, position ${i+1}">${c}</button>`).join('')}</div>`;}
function guidePracticeBoard(){return `<div class="wb-practice-letterboard" role="group" aria-label="All 26 letters">${alpha.map(letter=>`<button type="button" data-guide-letter="${letter}" class="${letter.toLowerCase()===demoWord[demoSelected]?'same':''} ${letter==='W'&&demoSelected===0?'suggested':''}" aria-label="Replace with ${letter}">${letter}</button>`).join('')}</div>`;}
function guidePractice(){const mode=helpInputMode,solved=demoSolved;
 return `<div class="wb-guide-scene wb-guide-practice-scene"><div class="wb-guide-copy wb-guide-practice-heading"><div class="wb-guide-kicker">TWO WAYS TO PLAY</div><h3>Make your move</h3><p>Choose a letter or type the whole next word.</p></div>
 <div class="wb-showcase wb-practice-showcase"><div class="wb-guide-modebar" role="group" aria-label="Input method"><button type="button" data-guide-mode="tap" class="${mode==='tap'?'active':''}" aria-pressed="${mode==='tap'}">${guideIcon('tap')} Tap letters</button><button type="button" data-guide-mode="type" class="${mode==='type'?'active':''}" aria-pressed="${mode==='type'}">${guideIcon('keyboard')} Type word</button></div>
 <div class="wb-practice-goal">CARD <span aria-hidden="true">→</span> WARD</div>
 <div id="guidePracticeWord">${guidePracticeTiles()}</div>
 ${mode==='tap'?`<div class="wb-practice-prompt">${solved?'Target reached!':demoSelected<0?'Tap a letter in CARD.':'Choose a replacement letter.'}</div><div id="guideLetterBoard">${guidePracticeBoard()}</div>`:`<div class="wb-type-controls"><label for="guideWordInput">Type the next word</label><div class="wb-type-inputrow"><input id="guideWordInput" type="text" maxlength="4" placeholder="WARD" autocomplete="off" autocorrect="off" autocapitalize="characters" spellcheck="false" aria-label="Type a four-letter word"/><button type="button" id="guideTypeEnter">Enter ↵</button></div><div class="wb-type-tip">PC: type directly + Enter &nbsp;·&nbsp; Phone: tap TYPE</div></div>`}
 <div class="wb-practice-bottom"><span id="guidePracticeStatus" class="wb-practice-status" role="status" aria-live="polite">${solved?'✓ Great! You made WARD.':' '}</span><button type="button" class="wb-guide-reset" id="guideReset">Try again ↻</button></div></div></div>`;
}
function guideToolsPath(){const words=demoPath.slice();const target='warm',n=4;const count=Math.max(0,n-words.length);let html='';words.forEach((w,i)=>{const active=i===words.length-1;const letters=active?[...w.toUpperCase()].map((c,j)=>`<span class="wb-mini-letter ${demoHintIndex===j?'hinted':''}">${c}</span>`).join(''):w.toUpperCase();html+=`<div class="wb-mini-path-step ${active?'current':''}">${letters}${!active?'<span class="wb-mini-check">✓</span>':''}</div>`;if(i===words.length-1&&words.length<=4)html+='<span class="wb-mini-path-arrow">↓</span>';else if(i<words.length-1)html+='<span class="wb-mini-path-arrow">↓</span>'});
 for(let i=0;i<count;i++){html+=`<div class="wb-mini-path-empty">····</div><span class="wb-mini-path-arrow">↓</span>`;}
 html+=`<div class="wb-mini-path-step destination">${target.toUpperCase()}</div>`;return html;}
function guideTools(){return `<div class="wb-guide-scene wb-guide-tools-scene"><div class="wb-guide-copy"><div class="wb-guide-kicker">KEEP PLAYING</div><h3>Find your own path</h3><p>Blank cards show the shortest path. <b>Extra moves are allowed.</b></p><div class="wb-guide-rulechips"><span>No timer or move limit</span><span>Invalid words don't count</span></div></div>
 <div class="wb-showcase wb-tools-showcase"><div class="wb-tools-demo"><div class="wb-mini-path" id="guideMiniPath">${guideToolsPath()}</div>
 <div class="wb-tools-action"><div class="wb-tools-pill"><button type="button" id="guideUndoDemo">${guideIcon('undo')} Undo</button><button type="button" id="guideHintDemo">${guideIcon('hint')} Hint</button></div><div id="guideToolStatus" role="status" aria-live="polite" class="wb-tool-status">Try the buttons.</div><button class="wb-guide-reset" type="button" id="guideExtraDemo">Show extra move +</button></div></div>
 <div class="wb-guide-toolnotes"><div><strong>Undo</strong><span>Return to the previous word.</span></div><div><strong>Hint</strong><span>First hint shows a letter change. More help: video step or manual clues.</span></div><div><strong>Progress</strong><span>Auto-saved. Restart from Settings.</span></div></div></div></div>`;}
function renderHelpStep(){const sceneRoot=$('guideScene');if(!sceneRoot)return;guideProgress();
 sceneRoot.scrollTop=0;
 sceneRoot.innerHTML=[guideSceneGoal,guidePractice,guideTools][helpStep]();$('guideBack').disabled=helpStep===0;
 $('guideNext').innerHTML=helpStep===2?(scene==='game'?'Back to Game <span aria-hidden="true">✓</span>':'Play <span aria-hidden="true">→</span>'):'Next <span aria-hidden="true">→</span>';
}
function guideSetStatus(msg){const target=$('guidePracticeStatus');if(target)target.textContent=msg;}
function guideCheckWord(next){next=next.toLowerCase().trim();if(next.length!==4){guideSetStatus('Enter a 4-letter word.');return;}
 if(!isMove(demoWord,next)){guideSetStatus('Change exactly one letter.');return;}
 if(!accepted.get(4).has(next)){guideSetStatus('That isn\'t an accepted word.');return;}
 demoWord=next;demoSelected=-1;demoSolved=demoWord==='ward';
 const row=$('guidePracticeWord');if(row)row.innerHTML=guidePracticeTiles();const board=$('guideLetterBoard');if(board)board.innerHTML=guidePracticeBoard();
 const prompt=document.querySelector('.wb-practice-prompt');if(prompt)prompt.textContent=demoSolved?'Target reached!':'Valid word! Now reach WARD.';
 guideSetStatus(demoSolved?'✓ Target reached!':'✓ Valid word! Keep going.');
}
function guideAction(button){if(!button)return false;
 // Dismiss a mobile virtual keyboard before changing demonstration scenes.
 if(button.id==='guideNext'||button.id==='guideBack'||button.dataset.guidePage!==undefined||button.dataset.guideMode){if(document.activeElement?.id==='guideWordInput')document.activeElement.blur();}
 if(button.dataset.guidePage!==undefined){helpStep=Number(button.dataset.guidePage);guideResetPractice();guideResetTools();renderHelpStep();return true;}
 if(button.id==='guideBack'){helpStep=Math.max(0,helpStep-1);guideResetPractice();guideResetTools();renderHelpStep();return true;}
 if(button.id==='guideNext'){if(helpStep===2){const fromGame=scene==='game';closeDialog();if(!fromGame)startGame();}else{helpStep++;guideResetPractice();guideResetTools();renderHelpStep();}return true;}
 if(button.hasAttribute('data-guide-replay')){helpAnimNonce++;renderHelpStep();return true;}
 if(button.dataset.guideMode){helpInputMode=button.dataset.guideMode;guideResetPractice();renderHelpStep();return true;}
 if(button.dataset.guidePos!==undefined){demoSelected=Number(button.dataset.guidePos);const row=$('guidePracticeWord');if(row)row.innerHTML=guidePracticeTiles();const board=$('guideLetterBoard');if(board)board.innerHTML=guidePracticeBoard();return true;}
 if(button.dataset.guideLetter){if(demoSelected<0){guideSetStatus('Tap a tile in the word first.');return true;}
 const next=demoWord.slice(0,demoSelected)+button.dataset.guideLetter.toLowerCase()+demoWord.slice(demoSelected+1);guideCheckWord(next);return true;}
 if(button.id==='guideReset'){guideResetPractice();renderHelpStep();return true;}
 if(button.id==='guideTypeEnter'){guideConfirmTyped();return true;}
 if(button.id==='guideUndoDemo'){if(demoPath.length>1){demoPath.pop();demoHintIndex=-1;$('guideMiniPath').innerHTML=guideToolsPath();$('guideToolStatus').textContent='Undid the last step.';}else $('guideToolStatus').textContent='You are back at the start.';return true;}
 if(button.id==='guideHintDemo'){demoHintIndex=changedIndex(demoPath.at(-1),demoPath.at(-1)==='cold'?'cord':demoPath.at(-1)==='cord'?'card':'ward');$('guideToolStatus').textContent=`Change ${demoPath.at(-1)[demoHintIndex].toUpperCase()} to ${(demoPath.at(-1)==='cold'?'cord':demoPath.at(-1)==='cord'?'card':'ward')[demoHintIndex].toUpperCase()}.`;$('guideMiniPath').innerHTML=guideToolsPath();return true;}
 if(button.id==='guideExtraDemo'){const options=['cord','card','ward'];const next=options[demoPath.length-1];if(next){demoPath.push(next);demoHintIndex=-1;$('guideMiniPath').innerHTML=guideToolsPath();$('guideToolStatus').textContent='Another valid step added.';}else {$('guideToolStatus').textContent='Reach WARM to finish the path.';}return true;}
 return false;
}
function guideConfirmTyped(){const input=$('guideWordInput');if(!input)return;guideCheckWord(input.value);if(demoSolved)input.blur();else input.focus();}

function openDialog(kind){$('wordInput').blur();dialogOpen=true;const wrap=$('dialogContent');document.querySelector('.dialog').classList.toggle('help-dialog',kind==='help');if(kind==='settings'){
 wrap.innerHTML=`<h2 id="dialogTitle">Settings</h2>
 <div class="dialog-row"><span>♪ &nbsp; Music</span><button class="switch ${settings.music?'on':''}" data-toggle="music" type="button" aria-pressed="${settings.music}">${settings.music?'ON':'OFF'}</button></div>
 <div class="dialog-row"><span>♫ &nbsp; Sound effects</span><button class="switch ${settings.sfx?'on':''}" data-toggle="sfx" type="button" aria-pressed="${settings.sfx}">${settings.sfx?'ON':'OFF'}</button></div>
 <div class="dialog-row"><span>◌ &nbsp; Reduced motion</span><button class="switch ${settings.reducedMotion?'on':''}" data-toggle="reducedMotion" type="button" aria-pressed="${settings.reducedMotion}">${settings.reducedMotion?'ON':'OFF'}</button></div>
 <button class="dialog-button" id="settingsHelp" type="button">How to play</button>
 ${scene==='game'?'<button class="dialog-button warning-button" id="restartRequest" type="button">Restart current level</button>':''}
 <p class="about-copy">Made by Oddberry Studios</p>`;
 }else if(kind==='help'){
  wrap.innerHTML=guideFrame();
  helpStep=0;helpInputMode='tap';guideResetPractice();guideResetTools();
  renderHelpStep();
 }else if(kind==='restart'){
 wrap.innerHTML=`<h2 id="dialogTitle">Start Over?</h2><p>Your current word path will reset. Your overall level progress will stay saved.</p><button class="dialog-button warning-button" id="restartConfirm" type="button">Restart level</button><button class="dialog-button" id="dialogCancel" type="button">Keep playing</button>`;
 }
 show($('dialogBackdrop'));$('dialogClose').focus();}
function closeDialog(){hide($('dialogBackdrop'));dialogOpen=false;}
$('dialogContent').addEventListener('keydown',ev=>{if(ev.target?.id==='guideWordInput'&&ev.key==='Enter'){ev.preventDefault();guideConfirmTyped();}});
$('dialogContent').addEventListener('input',ev=>{if(ev.target?.id==='guideWordInput')ev.target.value=ev.target.value.replace(/[^a-z]/gi,'').slice(0,4).toUpperCase();});
$('dialogContent').addEventListener('click',ev=>{const b=ev.target.closest('button');if(!b)return;if(guideAction(b))return;if(b.dataset.toggle){const name=b.dataset.toggle;setSettings({[name]:!settings[name]});sound.unlock();sound.applySettings();openDialog('settings');sound.effect('select');return;}if(b.id==='settingsHelp'){openDialog('help');return;}if(b.id==='restartRequest'){openDialog('restart');return;}if(b.id==='restartConfirm'){clearDraft();mobileTyping=false;clearFeedback();chain=[levelAt(levelNumber).start];freeHintUsed=false;fallbackHintWord='';fallbackHintStage=0;adFallbackActive=false;selectedIndex=null;hintPosition=-1;strongHintWord='';solutionCache=null;hide($('hintBanner'));save();closeDialog();render();toast('Level restarted.');return;}if(['dialogGotIt','dialogCancel'].includes(b.id))closeDialog();});
$('dialogClose').addEventListener('click',closeDialog);
$('dialogBackdrop').addEventListener('click',ev=>{if(ev.target===$('dialogBackdrop'))closeDialog()});
$('playButton').addEventListener('click',startGame);$('menuHelp').addEventListener('click',()=>openDialog('help'));$('menuSettings').addEventListener('click',()=>openDialog('settings'));$('homeButton').addEventListener('click',goHome);$('gameSettings').addEventListener('click',()=>openDialog('settings'));$('undoButton').addEventListener('click',undo);$('hintButton').addEventListener('click',requestHint);$('nextButton').addEventListener('click',nextLevel);
$('typeModeToggle').addEventListener('click',toggleTyping);$('typeSubmit').addEventListener('click',confirmTyped);
$('wordInput').addEventListener('input',ev=>{const word=ev.target.value.replace(/[^a-z]/gi,'').slice(0,chain.at(-1).length);ev.target.value=word.toUpperCase();typedDraft=word.toLowerCase();selectedIndex=null;clearFeedback();renderTiles();$('undoButton').disabled=chain.length<=1&&!typedDraft;});
$('wordInput').addEventListener('keydown',ev=>{if(ev.key==='Enter'){ev.preventDefault();confirmTyped()}if(ev.key==='Escape'){ev.preventDefault();clearDraft();clearFeedback();renderTiles();}});
document.addEventListener('keydown',ev=>{
 if(dialogOpen){if(ev.key==='Escape')closeDialog();return;}
 if(completeOpen){if(ev.key==='Enter'){ev.preventDefault();nextLevel();}return;}
 if(scene!=='game')return;
 if(ev.target?.matches('input,textarea,[contenteditable]'))return;
 if((ev.ctrlKey||ev.metaKey)&&ev.key.toLowerCase()==='z'){ev.preventDefault();undo();return;}
 if(ev.key==='Escape'){ev.preventDefault();clearDraft();selectedIndex=null;clearFeedback();renderTiles();renderAlpha();return;}
 if(ev.key==='Backspace'&&!ev.altKey&&!ev.ctrlKey&&!ev.metaKey){if(typedDraft){ev.preventDefault();typedDraft=typedDraft.slice(0,-1);clearFeedback();renderTiles();$('undoButton').disabled=chain.length<=1&&!typedDraft;}return;}
 if(ev.key==='Enter'&&typedDraft){ev.preventDefault();confirmTyped();return;}
 if(/^[a-z]$/i.test(ev.key)&&!ev.altKey&&!ev.ctrlKey&&!ev.metaKey){
  ev.preventDefault();if(typedDraft.length>=chain.at(-1).length){clearDraft();clearFeedback();}
  typedDraft+=ev.key.toLowerCase();selectedIndex=null;sound.effect('select');renderTiles();renderAlpha();$('undoButton').disabled=false;
 }
});
document.addEventListener('visibilitychange',()=>{if(document.hidden)sound.pause();else if(!pausedForAd)sound.resume()});

// Accommodate mobile browser toolbars and the on-screen keyboard without clipping controls.
function syncVisibleGameHeight(){
 const vp=window.visualViewport;
 const keyboardShown=!!(vp && (window.innerHeight-vp.height)>90 && vp.scale<=1.1);
 document.body.classList.toggle('wb-keyboard-open',keyboardShown);
 if(keyboardShown)document.documentElement.style.setProperty('--wb-visual-height',Math.max(230,Math.round(vp.height))+'px');
 else document.documentElement.style.removeProperty('--wb-visual-height');
}
window.addEventListener('resize',syncVisibleGameHeight,{passive:true});
window.visualViewport?.addEventListener('resize',syncVisibleGameHeight,{passive:true});
window.visualViewport?.addEventListener('scroll',syncVisibleGameHeight,{passive:true});
$('wordInput').addEventListener('focus',()=>{
 requestAnimationFrame(()=>{if(document.body.classList.contains('wb-keyboard-open'))$('wordInput').scrollIntoView({block:'nearest'});});
});
syncVisibleGameHeight();

// Test inspection hook is enabled only when explicitly requested, not in normal play.
if(new URLSearchParams(location.search).has('test'))window.__WB_TEST__={data,levelAt,accepted,familiar,legalChain,friendlyNext,getState:()=>({levelNumber,chain:chain.slice(),freeHintUsed,firstMoveLearned,fallbackHintStage,adFallbackActive,selectedIndex,hintPosition,strongHintWord,typedDraft,mobileTyping,scene,completeOpen,helpStep,bankRevision:BANK_REV,pinnedLevelId:pinnedLevel?.id||null,adaptiveBlock,helpOpen:dialogOpen&&document.querySelector('.dialog').classList.contains('help-dialog')}),setLevel:num=>{pinnedLevel=null;levelNumber=num;ensureBlock(num);chain=[levelAt(num).start];clearDraft();mobileTyping=false;freeHintUsed=false;fallbackHintWord='';fallbackHintStage=0;adFallbackActive=false;selectedIndex=null;hintPosition=-1;strongHintWord='';solutionCache=null;completeOpen=false;hide($('hintBanner'));hide($('completionBackdrop'));save();openScreen('game')}};
openScreen('menu');
})();
