const VERSION = 'v2025-10-24b-rectfill';

/* =================== Responsive sizing (full-screen) =================== */
let CAN_W = 400, CAN_H = 700;
function computeSize(){ CAN_W = window.innerWidth; CAN_H = window.innerHeight; }

/* =================== Game config (scales with level) =================== */
let cellW, cellH;      // rectangular cell size (px) — fills full screen
let PATH_W;            // visual path width (px), based on smaller of cellW/cellH
let BALL_R;            // ball radius
let GOAL_R;            // goal dot radius (50% of ball)
let level = 1;
let difficulty = 'medium'; // 'easy' | 'medium' | 'hard'

// physics
const GRAVITY = 0.32;
const FRICTION = 0.992;
const BOUNCE = 0.25;
let pos = {x:0,y:0}, vel = {x:0,y:0}, acc = {x:0,y:0};
let usingOrientation = false, havePermission = false;
let started = false;

// maze
let gridW, gridH;
let mazeEdges = [];
let startCell, endCell;
let startPos, endPos;
let solved = false;

// collision mask for BALL CENTER (eroded by BALL_R)
let centerMask;

/* =================== Utilities =================== */
function fadeOut(el){
  el.classList.add('fade-out');
  el.addEventListener('transitionend', ()=>{
    el.classList.add('hidden');
    el.setAttribute('aria-hidden','true');
  }, {once:true});
}
function isIOS(){
  return /iPad|iPhone|iPod/.test(navigator.userAgent) ||
         (navigator.platform === 'MacIntel' && navigator.maxTouchPoints>1);
}

/* =================== Maze generation (Wilson's Algorithm - robust) =================== */
function generateMaze(cols, rows){
  const H=rows, W=cols;
  const inTree = Array.from({length:H},()=>Array(W).fill(false));
  const dirs = [[1,0],[-1,0],[0,1],[0,-1]]; // R L D U
  const neighbors = (i,j)=>{
    const out=[];
    for(const [dx,dy] of dirs){
      const ni=i+dy, nj=j+dx;
      if(ni>=0&&nj>=0&&ni<H&&nj<W) out.push([ni,nj]);
    }
    return out;
  };
  // seed with one random cell
  const si = Math.floor(Math.random()*H), sj=Math.floor(Math.random()*W);
  inTree[si][sj]=true;
  const parent = Array.from({length:H},()=>Array(W).fill(null));
  const total = H*W; let added = 1;

  while(added < total){
    // pick a random unvisited start
    let ui, uj;
    do { ui=Math.floor(Math.random()*H); uj=Math.floor(Math.random()*W);} while(inTree[ui][uj]);

    // loop-erased random walk to existing tree
    const path=[]; const index=new Map();
    let ci=ui, cj=uj; path.push([ci,cj]); index.set(ci+','+cj,0);
    while(!inTree[ci][cj]){
      const opts = neighbors(ci,cj);
      const [ni,nj] = opts[Math.floor(Math.random()*opts.length)];
      const key = ni+','+nj;
      if(index.has(key)){
        const cut = index.get(key);
        path.length = cut+1; // erase loop
      } else {
        path.push([ni,nj]); index.set(key, path.length-1);
      }
      ci=ni; cj=nj;
    }
    // add path to tree; track parents (we'll make undirected set later)
    for(let k=0;k<path.length-1;k++){
      const [a1,b1]=path[k], [a2,b2]=path[k+1];
      if(!inTree[a1][b1]){ inTree[a1][b1]=true; added++; parent[a1][b1]=a2+','+b2; }
      if(!inTree[a2][b2]){ inTree[a2][b2]=true; added++; parent[a2][b2]=a1+','+b1; }
    }
  }

  // undirected passages
  const passages = new Set();
  for(let i=0;i<H;i++) for(let j=0;j<W;j++){
    const p = parent[i][j]; if(!p) continue; const [pi,pj]=p.split(',').map(Number);
    const a=`${i},${j}`, b=`${pi},${pj}`; passages.add(a+"-"+b); passages.add(b+"-"+a);
  }

  // pick far endpoints via BFS
  function cellToIdx(i,j){ return i*W + j; }
  const adj = Array.from({length:H*W},()=>[]);
  for(let i=0;i<H;i++)for(let j=0;j<W;j++){
    const id=cellToIdx(i,j);
    for(const [dx,dy] of [[1,0],[0,1],[-1,0],[0,-1]]){
      const ni=i+dy,nj=j+dx; if(ni<0||nj<0||ni>=H||nj>=W) continue;
      if(passages.has(`${i},${j}-${ni},${nj}`)) adj[id].push(cellToIdx(ni,nj));
    }
  }
  function bfs(start){
    const dist=Array(H*W).fill(Infinity); dist[start]=0; const q=[start];
    while(q.length){
      const v=q.shift();
      for(const w of adj[v]){
        if(dist[w]===Infinity){ dist[w]=dist[v]+1; q.push(w); }
      }
    }
    return dist;
  }
  const s0=0, d0=bfs(s0); let a=0; for(let k=0;k<d0.length;k++) if(d0[k]>d0[a]) a=k;
  const d1=bfs(a); let b=0; for(let k=0;k<d1.length;k++) if(d1[k]>d1[b]) b=k; // (fixed small typo from earlier message)
  const ai=Math.floor(a/W), aj=a%W, bi=Math.floor(b/W), bj=b%W;
  return {passages, start:{i:ai,j:aj}, end:{i:bi,j:bj}, cols:W, rows:H};
}

/* =================== Geometry that fills the screen (rectangular cells) =================== */
function buildMazeGeometry(){
  // 1) Choose a *target* cell size from difficulty (unchanged)
  const target = (difficulty==='easy') ? 54 : (difficulty==='hard' ? 28 : 36);
  const baseCell = Math.max(18, target - Math.max(0, level-1));

  // 2) Start by sizing to WIDTH with ~1-cell margin on each side
  //    This locks square cells and ensures we fill width nicely.
  let gridW = Math.max(8, Math.floor(CAN_W / baseCell) - 2);
  let cellSize = Math.floor(CAN_W / (gridW + 2));  // ← square cell size from width

  // 3) With that *same* square cell size, compute how many rows fit vertically
  //    (keeping ~1-cell margin top & bottom)
  let gridH = Math.max(8, Math.floor(CAN_H / cellSize) - 2);

  // 4) Grow rows to reduce vertical margin while we still fit on screen.
  //    (Total height used = (gridH + 2) * cellSize. Add rows while adding 1 more still fits.)
  while ( (gridH + 3) * cellSize <= CAN_H ) gridH++;

  // (Optional) If there’s horizontal slack, you can also grow columns similarly:
  // while ( (gridW + 3) * cellSize <= CAN_W ) gridW++;

  // 5) Offsets to center the maze (now margins should be small on tall screens)
  const offsetX = Math.floor((CAN_W - (gridW + 2) * cellSize) / 2);
  const offsetY = Math.floor((CAN_H - (gridH + 2) * cellSize) / 2);

  // 6) Derive path/ball sizes from the (square) cell size
  PATH_W = Math.floor(cellSize * 0.56);
  BALL_R = Math.floor(PATH_W * 0.45);
  GOAL_R = Math.floor(BALL_R * 0.5);

  // 7) Generate the maze edges using the new gridW/gridH
  const m = generateMaze(gridW, gridH);
  const { start, end } = m;

  mazeEdges = [];
  function cellCenter(i, j){
    const x = cellSize * (j + 1) + cellSize / 2 + offsetX;
    const y = cellSize * (i + 1) + cellSize / 2 + offsetY;
    return { x, y };
  }

  for (let i = 0; i < gridH; i++){
    for (let j = 0; j < gridW; j++){
      // draw right & down edges of the passage graph
      for (const [dx, dy] of [[1,0],[0,1]]) {
        const ni = i + dy, nj = j + dx;
        if (ni >= gridH || nj >= gridW) continue;
        if (m.passages.has(`${i},${j}-${ni},${nj}`)) {
          const A = cellCenter(i, j), B = cellCenter(ni, nj);
          mazeEdges.push([A, B]);
        }
      }
    }
  }

  // 8) Start/goal positions and physics reset
  startPos = cellCenter(start.i, start.j);
  endPos   = cellCenter(end.i,   end.j);
  pos = { x: startPos.x, y: startPos.y };
  vel = { x: 0, y: 0 };
  solved = false;

  // 9) Rebuild the collision mask based on the new geometry
  buildCollisionMask();
}


function buildCollisionMask(){
  // Eroded mask for BALL CENTER (prevents edge overlap)
  const cCanvas = document.createElement('canvas');
  cCanvas.width = CAN_W; cCanvas.height = CAN_H;
  const cctx = cCanvas.getContext('2d');
  cctx.clearRect(0,0,CAN_W,CAN_H);
  cctx.fillStyle='#000'; cctx.fillRect(0,0,CAN_W,CAN_H);
  cctx.lineCap='round'; cctx.lineJoin='round';
  const eroded = Math.max(1, PATH_W - 2*BALL_R + 2); // +2px safety
  cctx.lineWidth = eroded; cctx.strokeStyle='#fff';
  for(const [A,B] of mazeEdges){
    cctx.beginPath(); cctx.moveTo(A.x, A.y); cctx.lineTo(B.x, B.y); cctx.stroke();
  }
  centerMask = cctx.getImageData(0,0,CAN_W,CAN_H).data;
}

function pointInsideCenterMask(x,y){
  const ix = Math.max(0, Math.min(CAN_W-1, Math.round(x)));
  const iy = Math.max(0, Math.min(CAN_H-1, Math.round(y)));
  return centerMask[(iy*CAN_W + ix)*4] > 127;
}

/* =================== Rendering =================== */
function drawPaths(ctx){
  ctx.fillStyle='#ffffff'; ctx.fillRect(0,0,CAN_W,CAN_H);
  ctx.lineCap='round'; ctx.lineJoin='round'; ctx.lineWidth=PATH_W; ctx.strokeStyle='#d7d7db';
  for(const [A,B] of mazeEdges){ ctx.beginPath(); ctx.moveTo(A.x,A.y); ctx.lineTo(B.x,B.y); ctx.stroke(); }
}
function drawGoal(ctx){
  ctx.fillStyle='#f59e0b';
  ctx.beginPath(); ctx.arc(endPos.x, endPos.y, GOAL_R, 0, Math.PI*2); ctx.fill();
}
function drawBall(ctx){
  ctx.fillStyle='#e11d48';
  ctx.beginPath(); ctx.arc(pos.x, pos.y, BALL_R, 0, Math.PI*2); ctx.fill();
}

/* =================== p5 Sketch =================== */
function setup(){
  computeSize();
  const c = createCanvas(CAN_W, CAN_H); c.parent('wrap');
  pixelDensity(Math.min(2, window.devicePixelRatio||1));
  initSplash();
  setupOrientationGuard();
  window.addEventListener('resize', onResize, {passive:true});
  document.getElementById('splashVersion').textContent = VERSION;
  document.getElementById('verTag')?.append?.(document.createTextNode(VERSION));

  // Global safety net: first user gesture anywhere starts the game (for iOS)
  const firstGesture = (ev)=>{ beginGame(ev); cleanup(); };
  const cleanup = ()=>{
    document.removeEventListener('touchstart', firstGesture, {capture:true});
    document.removeEventListener('pointerdown', firstGesture, {capture:true});
    document.removeEventListener('mousedown', firstGesture, {capture:true});
  };
  document.addEventListener('touchstart', firstGesture, {capture:true, passive:false});
  document.addEventListener('pointerdown', firstGesture, {capture:true});
  document.addEventListener('mousedown', firstGesture, {capture:true});
}

function onResize(){
  computeSize(); resizeCanvas(CAN_W, CAN_H);
  if (centerMask){ buildMazeGeometry(); }
}

function draw(){
  const ctx = this.drawingContext;
  if(!centerMask){ ctx.fillStyle='#fff'; ctx.fillRect(0,0,CAN_W,CAN_H); return; }
  drawPaths(ctx);
  drawGoal(ctx);

  // physics
  let ax=0, ay=0; if(usingOrientation){ ax+=acc.x; ay+=acc.y; }
  vel.x = (vel.x + ax) * FRICTION; vel.y = (vel.y + ay) * FRICTION;
  let nx = pos.x + vel.x, ny = pos.y + vel.y;
  if(pointInsideCenterMask(nx,ny)){
    pos.x = nx; pos.y = ny;
  } else {
    const tryX = pointInsideCenterMask(pos.x + vel.x, pos.y);
    const tryY = pointInsideCenterMask(pos.x, pos.y + vel.y);
    if(tryX) pos.x += vel.x; else vel.x *= -BOUNCE;
    if(tryY) pos.y += vel.y; else vel.y *= -BOUNCE;
  }

  drawBall(ctx);

  // goal check
  const d = Math.hypot(pos.x-endPos.x, pos.y-endPos.y);
  if(!solved && d < GOAL_R*0.9){ solved = true; showCongrats(); }
}

function nextLevel(){ level++; buildMazeGeometry(); solved=false; }

/* =================== Device Orientation =================== */
function handleOrientation(e){
  const g = e.gamma ?? 0; const b = e.beta ?? 0;
  acc.x = GRAVITY * Math.sin(g*Math.PI/180);
  acc.y = GRAVITY * Math.sin(b*Math.PI/180);
}
async function askPermission(){
  try{
    let granted = false;
    if (typeof DeviceOrientationEvent !== 'undefined' && typeof DeviceOrientationEvent.requestPermission === 'function'){
      const p1 = await DeviceOrientationEvent.requestPermission();
      if (p1 === 'granted'){ window.addEventListener('deviceorientation', handleOrientation, true); granted = true; }
    } else {
      // Non-iOS: just attach
      window.addEventListener('deviceorientation', handleOrientation, true);
      granted = true;
    }
    if (typeof DeviceMotionEvent !== 'undefined' && typeof DeviceMotionEvent.requestPermission === 'function'){
      try { await DeviceMotionEvent.requestPermission(); } catch {}
    }
    if (granted){ havePermission = true; usingOrientation = true; }
  }catch(err){ console.warn('Permission error', err); }
}
function startOrientation(){
  window.addEventListener('deviceorientation', handleOrientation, true);
  usingOrientation = true;
}

/* =================== Splash / Start / Congrats =================== */
async function beginGame(ev){
  if (started) return;
  started = true;
  try { ev?.preventDefault?.(); ev?.stopPropagation?.(); } catch {}
  const needsPerm = isIOS()
    && typeof DeviceOrientationEvent !== 'undefined'
    && typeof DeviceOrientationEvent.requestPermission === 'function';
  try{
    if (needsPerm) { await askPermission(); }
    else { startOrientation(); }
  } catch(e){ console.warn('permission error', e); }
  // Build maze and fade splash regardless (don’t strand the user)
  buildMazeGeometry();
  const splash = document.getElementById('splash');
  splash.classList.add('fade-out');
  splash.setAttribute('aria-hidden','true');
}
window.beginGame = beginGame;

function initSplash(){
  const splash = document.getElementById('splash');
  const btn = document.getElementById('beginBtn');

  // Detect if iOS requires explicit permission prompts
  const needsPerm = isIOS()
    && typeof DeviceOrientationEvent !== 'undefined'
    && typeof DeviceOrientationEvent.requestPermission === 'function';

  // Single, explicit handler (mirrors v12 "working" behavior)
  const startNow = async (e)=>{
    if (started) return;
    started = true;
    try { e?.preventDefault?.(); e?.stopPropagation?.(); } catch {}
    try{
      if (needsPerm) { await askPermission(); }
      else { startOrientation(); }
    } catch(err){ console.warn('permission error', err); }
    buildMazeGeometry();
    splash.classList.add('fade-out');
    splash.setAttribute('aria-hidden','true');
  };

  // Button: click & touchstart (no inline attributes needed)
  if (btn){
    btn.addEventListener('click',      startNow, {once:true, passive:false});
    btn.addEventListener('touchstart', startNow, {once:true, passive:false});
    btn.addEventListener('pointerdown',startNow, {once:true, passive:false});
  }

  // Background tap to start as well (optional)
  const bgStart = (e)=>{ if (e.target===splash) startNow(e); };
  splash.addEventListener('click',       bgStart, {passive:false, once:true});
  splash.addEventListener('touchstart',  bgStart, {passive:false, once:true});
  splash.addEventListener('pointerdown', bgStart, {passive:false, once:true});
}


function showCongrats(){
  const cg = document.getElementById('congrats');
  cg.classList.remove('hidden');
  cg.classList.remove('fade-out');
  cg.setAttribute('aria-hidden','false');
  const hook = (d)=>()=>{
    difficulty = d; level = 1;
    cg.classList.add('fade-out');
    cg.addEventListener('transitionend', ()=>{
      cg.classList.add('hidden');
      cg.setAttribute('aria-hidden','true');
      buildMazeGeometry(); solved=false;
    }, {once:true});
  };
  document.getElementById('againEasy').onclick = hook('easy');
  document.getElementById('againMed').onclick  = hook('medium');
  document.getElementById('againHard').onclick = hook('hard');
}

/* =================== Portrait guard =================== */
let mql;
function setupOrientationGuard(){
  mql = window.matchMedia('(orientation: landscape)');
  mql.addEventListener('change', updateOrientationGuard);
  updateOrientationGuard();
}
function updateOrientationGuard(){
  const rot = document.getElementById('rotate');
  if (window.matchMedia('(orientation: landscape)').matches){ rot.classList.add('show'); }
  else { rot.classList.remove('show'); }
}


