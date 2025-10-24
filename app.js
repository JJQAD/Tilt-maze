// Announce parse success ASAP (lets the badge flip to JS: OK even if later code fails)
if (typeof window !== 'undefined' && typeof window.__bootJSReady === 'function') {
  window.__bootJSReady('parse');
}

var VERSION = 'v2025-10-24h';

// =============== Responsive sizing ===============
var CAN_W = 400, CAN_H = 700;
function computeSize(){ CAN_W = window.innerWidth; CAN_H = window.innerHeight; }

// =============== Game config ===============
var cellW, cellH;
var PATH_W, BALL_R, GOAL_R;
var level = 1;
var difficulty = 'medium';
var GRAVITY = 0.32, FRICTION = 0.992, BOUNCE = 0.25;
var pos = {x:0,y:0}, vel = {x:0,y:0}, acc = {x:0,y:0};
var usingOrientation = false, havePermission = false, started = false;

// Maze
var gridW, gridH, mazeEdges = [];
var startCell, endCell, startPos, endPos;
var solved = false;
var centerMask; // collision mask for ball center

// =============== Helpers ===============
function isIOS(){
  return /iPad|iPhone|iPod/.test(navigator.userAgent) ||
         (navigator.platform === 'MacIntel' && navigator.maxTouchPoints>1);
}
function badgeNote(msg){
  var b=document.getElementById('bootBadge');
  if(!b) return;
  var l=b.innerHTML.split('<br>');
  l[1]='JS: '+msg;
  b.innerHTML=l.join('<br>');
}

// =============== Maze generation (Wilson) ===============
function generateMaze(cols, rows){
  var H = rows, W = cols;
  var inTree = Array.from({length:H}, function(){ return Array(W).fill(false); });
  var dirs = [[1,0],[-1,0],[0,1],[0,-1]];
  function neighbors(i,j){
    var out=[], k, ni, nj, d;
    for(k=0;k<dirs.length;k++){
      d = dirs[k]; ni=i+d[1]; nj=j+d[0];
      if(ni>=0 && nj>=0 && ni<H && nj<W) out.push([ni,nj]);
    }
    return out;
  }
  var si = Math.floor(Math.random()*H), sj=Math.floor(Math.random()*W);
  inTree[si][sj]=true;
  var parent = Array.from({length:H}, function(){ return Array(W).fill(null); });
  var total = H*W, added = 1;

  while(added < total){
    var ui, uj;
    do { ui=Math.floor(Math.random()*H); uj=Math.floor(Math.random()*W); } while(inTree[ui][uj]);
    var path=[], index={}, key, cut;
    var ci=ui, cj=uj; path.push([ci,cj]); index[ci+','+cj]=0;
    while(!inTree[ci][cj]){
      var opts = neighbors(ci,cj);
      var pick = opts[Math.floor(Math.random()*opts.length)];
      var ni=pick[0], nj=pick[1];
      key = ni+','+nj;
      if(index.hasOwnProperty(key)){
        cut = index[key]; path.length = cut+1;
      } else {
        path.push([ni,nj]); index[key] = path.length-1;
      }
      ci=ni; cj=nj;
    }
    for(var k=0;k<path.length-1;k++){
      var a1=path[k][0], b1=path[k][1], a2=path[k+1][0], b2=path[k+1][1];
      if(!inTree[a1][b1]){ inTree[a1][b1]=true; added++; parent[a1][b1]=a2+','+b2; }
      if(!inTree[a2][b2]){ inTree[a2][b2]=true; added++; parent[a2][b2]=a1+','+b1; }
    }
  }

  var passages = new Set();
  for(var i=0;i<H;i++) for(var j=0;j<W;j++){
    var p = parent[i][j]; if(!p) continue;
    var pi=parseInt(p.split(',')[0],10), pj=parseInt(p.split(',')[1],10);
    var a=i+','+j, b=pi+','+pj; passages.add(a+'-'+b); passages.add(b+'-'+a);
  }

  function cellToIdx(i,j){ return i*W + j; }
  var adj = Array.from({length:H*W}, function(){ return []; });
  for(i=0;i<H;i++) for(j=0;j<W;j++){
    var id = cellToIdx(i,j);
    var dlist = [[1,0],[0,1],[-1,0],[0,-1]];
    for(var d=0; d<dlist.length; d++){
      var dx=dlist[d][0], dy=dlist[d][1];
      var ni=i+dy, nj=j+dx;
      if(ni<0||nj<0||ni>=H||nj>=W) continue;
      if(passages.has(i+','+j+'-'+ni+','+nj)) adj[id].push(cellToIdx(ni,nj));
    }
  }
  function bfs(start){
    var dist=Array(H*W).fill(Infinity); dist[start]=0; var q=[start];
    while(q.length){
      var v=q.shift();
      for(var wIdx=0; wIdx<adj[v].length; wIdx++){
        var w=adj[v][wIdx];
        if(dist[w]===Infinity){ dist[w]=dist[v]+1; q.push(w); }
      }
    }
    return dist;
  }
  var s0=0, d0=bfs(s0), a=0;
  for(var k2=0;k2<d0.length;k2++) if(d0[k2]>d0[a]) a=k2;
  var d1=bfs(a), b=0;
  for(k2=0;k2<d1.length;k2++) if(d1[k2]>d1[b]) b=k2;
  var ai=Math.floor(a/W), aj=a%W, bi=Math.floor(b/W), bj=b%W;
  return {passages:passages, start:{i:ai,j:aj}, end:{i:bi,j:bj}, cols:W, rows:H};
}

// =============== Geometry ===============
function buildMazeGeometry(){
  var target = (difficulty==='easy') ? 54 : (difficulty==='hard' ? 28 : 36);

  gridW = Math.max(8, Math.floor(CAN_W / target));
  gridH = Math.max(8, Math.floor(CAN_H / target));

  var provisionalCellW = CAN_W / gridW;
  var provisionalCellH = CAN_H / gridH;
  PATH_W = Math.floor(Math.min(provisionalCellW, provisionalCellH) * 0.56);
  var margin = Math.ceil(PATH_W/2) + 2;
  var usableW = CAN_W - margin*2;
  var usableH = CAN_H - margin*2;

  cellW = usableW / gridW;
  cellH = usableH / gridH;

  PATH_W = Math.floor(Math.min(cellW, cellH) * 0.56);
  BALL_R = Math.floor(PATH_W * 0.45);
  GOAL_R = Math.floor(BALL_R * 0.5);

  var m = generateMaze(gridW, gridH);
  startCell = m.start; endCell = m.end;

  mazeEdges = [];
  function cellCenter(i,j){
    var x = margin + cellW*j + cellW/2;
    var y = margin + cellH*i + cellH/2;
    return {x:x,y:y};
  }
  for(var i=0;i<gridH;i++) for(var j=0;j<gridW;j++){
    var neigh = [[1,0],[0,1]];
    for(var nd=0; nd<neigh.length; nd++){
      var dx=neigh[nd][0], dy=neigh[nd][1];
      var ni=i+dy, nj=j+dx; if(ni>=gridH||nj>=gridW) continue;
      if(m.passages.has(i+','+j+'-'+ni+','+nj)){
        var A = cellCenter(i,j), B = cellCenter(ni,nj);
        mazeEdges.push([A,B]);
      }
    }
  }
  startPos = cellCenter(startCell.i, startCell.j);
  endPos   = cellCenter(endCell.i,   endCell.j);
  pos = {x:startPos.x, y:startPos.y}; vel={x:0,y:0};

  buildCollisionMask();
}

// =============== Collision Mask ===============
function buildCollisionMask(){
  var cCanvas = document.createElement('canvas');
  cCanvas.width = CAN_W; cCanvas.height = CAN_H;
  var cctx = cCanvas.getContext('2d');
  cctx.clearRect(0,0,CAN_W,CAN_H);
  cctx.fillStyle='#000'; cctx.fillRect(0,0,CAN_W,CAN_H);
  cctx.lineCap='round'; cctx.lineJoin='round';
  var eroded = Math.max(1, PATH_W - 2*BALL_R + 2);
  cctx.lineWidth = eroded; cctx.strokeStyle='#fff';
  for(var e=0;e<mazeEdges.length;e++){
    var A=mazeEdges[e][0], B=mazeEdges[e][1];
    cctx.beginPath(); cctx.moveTo(A.x, A.y); cctx.lineTo(B.x, B.y); cctx.stroke();
  }
  centerMask = cctx.getImageData(0,0,CAN_W,CAN_H).data;
}
function pointInsideCenterMask(x,y){
  var ix = Math.max(0, Math.min(CAN_W-1, Math.round(x)));
  var iy = Math.max(0, Math.min(CAN_H-1, Math.round(y)));
  return centerMask[(iy*CAN_W + ix)*4] > 127;
}

// =============== Rendering ===============
function drawPaths(ctx){
  ctx.fillStyle='#ffffff'; ctx.fillRect(0,0,CAN_W,CAN_H);
  ctx.lineCap='round'; ctx.lineJoin='round'; ctx.lineWidth=PATH_W; ctx.strokeStyle='#d7d7db';
  for(var e=0;e<mazeEdges.length;e++){
    var A=mazeEdges[e][0], B=mazeEdges[e][1];
    ctx.beginPath(); ctx.moveTo(A.x,A.y); ctx.lineTo(B.x,B.y); ctx.stroke();
  }
}
function drawGoal(ctx){
  ctx.fillStyle='#f59e0b';
  ctx.beginPath(); ctx.arc(endPos.x, endPos.y, GOAL_R, 0, Math.PI*2); ctx.fill();
}
function drawBall(ctx){
  ctx.fillStyle='#e11d48';
  ctx.beginPath(); ctx.arc(pos.x, pos.y, BALL_R, 0, Math.PI*2); ctx.fill();
}

// =============== p5 Sketch ===============
function setup(){
  computeSize();
  var c = createCanvas(CAN_W, CAN_H); c.parent('wrap');
  pixelDensity(Math.min(2, (window.devicePixelRatio||1)));
  initSplash();
  setupOrientationGuard();
  window.addEventListener('resize', onResize, {passive:true});
  var sv = document.getElementById('splashVersion'); if(sv) sv.textContent = VERSION;
  var vt = document.getElementById('verTag'); if(vt) vt.textContent = VERSION;

  // First gesture fallback (iOS); also visible badge update
  function firstGesture(ev){ badgeNote('tap-anywhere'); beginGame(ev); cleanup(); }
  function cleanup(){
    document.removeEventListener('touchstart', firstGesture, true);
    document.removeEventListener('pointerdown', firstGesture, true);
    document.removeEventListener('mousedown', firstGesture, true);
  }
  document.addEventListener('touchstart', firstGesture, true);
  document.addEventListener('pointerdown', firstGesture, true);
  document.addEventListener('mousedown', firstGesture, true);

  if (typeof window.__bootJSReady === 'function') window.__bootJSReady('boot');
}

function onResize(){
  computeSize(); resizeCanvas(CAN_W, CAN_H);
  if (centerMask){ buildMazeGeometry(); }
}

function draw(){
  var ctx = this.drawingContext;
  if(!centerMask){ ctx.fillStyle='#fff'; ctx.fillRect(0,0,CAN_W,CAN_H); return; }
  drawPaths(ctx);
  drawGoal(ctx);

  var ax=0, ay=0; if(usingOrientation){ ax+=acc.x; ay+=acc.y; }
  vel.x = (vel.x + ax) * FRICTION; vel.y = (vel.y + ay) * FRICTION;
  var nx = pos.x + vel.x, ny = pos.y + vel.y;
  if(pointInsideCenterMask(nx,ny)){
    pos.x = nx; pos.y = ny;
  } else {
    var tryX = pointInsideCenterMask(pos.x + vel.x, pos.y);
    var tryY = pointInsideCenterMask(pos.x, pos.y + vel.y);
    if(tryX) pos.x += vel.x; else vel.x *= -BOUNCE;
    if(tryY) pos.y += vel.y; else vel.y *= -BOUNCE;
  }

  drawBall(ctx);

  var d = Math.hypot(pos.x-endPos.x, pos.y-endPos.y);
  if(!solved && d < GOAL_R*0.9){ solved = true; showCongrats(); }
}

// =============== Device Orientation ===============
function handleOrientation(e){
  var g = (typeof e.gamma === 'number') ? e.gamma : 0;
  var b = (typeof e.beta  === 'number') ? e.beta  : 0;
  acc.x = GRAVITY * Math.sin(g*Math.PI/180);
  acc.y = GRAVITY * Math.sin(b*Math.PI/180);
}
async function askPermission(){
  try{
    var granted = false;
    if (typeof DeviceOrientationEvent !== 'undefined' && typeof DeviceOrientationEvent.requestPermission === 'function'){
      var p1 = await DeviceOrientationEvent.requestPermission();
      if (p1 === 'granted'){ window.addEventListener('deviceorientation', handleOrientation, true); granted = true; }
    } else {
      window.addEventListener('deviceorientation', handleOrientation, true);
      granted = true;
    }
    if (typeof DeviceMotionEvent !== 'undefined' && typeof DeviceMotionEvent.requestPermission === 'function'){
      try { await DeviceMotionEvent.requestPermission(); } catch(_){}
    }
    if (granted){ havePermission = true; usingOrientation = true; }
  }catch(err){ console.warn('Permission error', err); }
}
function startOrientation(){
  window.addEventListener('deviceorientation', handleOrientation, true);
  usingOrientation = true;
}

// =============== Splash / Start / Congrats ===============
async function beginGame(ev){
  if (started) { badgeNote('already-started'); return; }
  started = true;
  try { if(ev && ev.preventDefault) ev.preventDefault(); if(ev && ev.stopPropagation) ev.stopPropagation(); } catch(_){}
  badgeNote('start-handler');

  var needsPerm = isIOS()
    && typeof DeviceOrientationEvent !== 'undefined'
    && typeof DeviceOrientationEvent.requestPermission === 'function';
  try{
    if (needsPerm) { badgeNote('ask-permission'); await askPermission(); }
    else { badgeNote('start-orientation'); startOrientation(); }
  } catch(e){ console.warn('permission error', e); badgeNote('perm-error'); }

  buildMazeGeometry(); badgeNote('built-maze');

  var splash = document.getElementById('splash');
  if (splash){
    splash.classList.add('fade-out');
    splash.setAttribute('aria-hidden','true');
    badgeNote('faded-splash');
  } else {
    badgeNote('no-splash');
  }
}
window.beginGame = beginGame;

function initSplash(){
  var splash = document.getElementById('splash');
  var btn = document.getElementById('beginBtn');

  var needsPerm = isIOS()
    && typeof DeviceOrientationEvent !== 'undefined'
    && typeof DeviceOrientationEvent.requestPermission === 'function';

  async function startNow(e){
    if (started) { badgeNote('already-started'); return; }
    started = true;
    try { if(e && e.preventDefault) e.preventDefault(); if(e && e.stopPropagation) e.stopPropagation(); } catch(_){}
    badgeNote('startNow');

    try{
      if (needsPerm) { badgeNote('ask-permission'); await askPermission(); }
      else { badgeNote('start-orientation'); startOrientation(); }
    } catch(err){ console.warn('permission error', err); badgeNote('perm-error'); }

    buildMazeGeometry(); badgeNote('built-maze');
    if (splash){
      splash.classList.add('fade-out');
      splash.setAttribute('aria-hidden','true');
      badgeNote('faded-splash');
    }
  }

  if (btn){
    btn.addEventListener('click',      startNow, {once:true, passive:false});
    btn.addEventListener('touchstart', startNow, {once:true, passive:false});
    btn.addEventListener('pointerdown',startNow, {once:true, passive:false});
  }
  if (splash){
    function bgStart(e){ if (e && e.target === splash) startNow(e); }
    splash.addEventListener('click',       bgStart, {passive:false, once:true});
    splash.addEventListener('touchstart',  bgStart, {passive:false, once:true});
    splash.addEventListener('pointerdown', bgStart, {passive:false, once:true});
  }
}

function showCongrats(){
  var cg = document.getElementById('congrats');
  if(!cg) return;
  cg.classList.remove('hidden');
  cg.classList.remove('fade-out');
  cg.setAttribute('aria-hidden','false');
  function hook(d){
    return function(){
      difficulty = d; level = 1;
      cg.classList.add('fade-out');
      cg.addEventListener('transitionend', function(){
        cg.classList.add('hidden');
        cg.setAttribute('aria-hidden','true');
        buildMazeGeometry(); solved=false;
      }, {once:true});
    };
  }
  var eBtn=document.getElementById('againEasy'), mBtn=document.getElementById('againMed'), hBtn=document.getElementById('againHard');
  if(eBtn) eBtn.onclick = hook('easy');
  if(mBtn) mBtn.onclick  = hook('medium');
  if(hBtn) hBtn.onclick  = hook('hard');
}

// =============== Portrait guard ===============
var mql;
function setupOrientationGuard(){
  mql = window.matchMedia('(orientation: landscape)');
  if (mql && mql.addEventListener) mql.addEventListener('change', updateOrientationGuard);
  updateOrientationGuard();
}
function updateOrientationGuard(){
  var rot = document.getElementById('rotate');
  if (!rot) return;
  if (window.matchMedia('(orientation: landscape)').matches){ rot.classList.add('show'); }
  else { rot.classList.remove('show'); }
}
