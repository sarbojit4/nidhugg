/* Copyright (C) 2019-2023 Sarbojit Das
 *
 * This file is part of Nidhugg.
 *
 * Nidhugg is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Nidhugg is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see
 * <http://www.gnu.org/licenses/>.
 */

#include "Debug.h"
#include "EventTraceBuilder.h"
#include "TraceUtil.h"

#include <sstream>
#include <stdexcept>
#include <unordered_map>
#include <forward_list>

#define ANSIRed "\x1b[91m"
#define ANSIRst "\x1b[m"

static void clear_observed(sym_ty &syms);
static std::string events_to_string(const llvm::SmallVectorImpl<SymEv> &e);

EventTraceBuilder::EventTraceBuilder(const Configuration &conf) : TSOPSOTraceBuilder(conf) {
  threads.push_back(Thread(CPid(), -1));
  threads.push_back(Thread(CPS.new_aux(CPid()), -1));
  threads[1].available = false; // Store buffer is empty.
  threads[0].spid = 0;
  prefix_idx = -1;
  dryrun = false;
  replay = false;
  unfinished_message = 0;
  last_full_memory_conflict = -1;
  last_md = 0;
  replay_point = 0;
  end_of_ws = -1;
}

EventTraceBuilder::~EventTraceBuilder(){
}

bool EventTraceBuilder::schedule(int *proc, int *aux, int *alt, bool *dryrun){
  assert(!has_vclocks && "Can't add more events after analysing the trace");

  *dryrun = false;
  *alt = 0;
  this->dryrun = false;
  if(replay){
    /* Are we done with the current Event? */
    if(0 <= prefix_idx && threads[curev().iid.get_pid()].last_event_index() <
       curev().iid.get_index() + curbranch().size - 1){
      /* Continue executing the current Event */
      IPid pid = curev().iid.get_pid();
      //llvm::dbgs()<<"Scheduling1 "<<threads[pid].cpid<<"\n";////////////////////
      *proc = pid/2;
      *aux = pid % 2 - 1;
      *alt = 0;
      assert(threads[pid].available);
      threads[pid].event_indices.push_back(prefix_idx);
      return true;
    }else if(prefix_idx + 1 == int(prefix.len()) && prefix.lastnode().size() == 0){

      /* We are done replaying. Continue below... */
      assert(prefix_idx < 0 || curev().sym.size() == sym_idx
             || (errors.size() && errors.back()->get_location()
                 == IID<CPid>(threads[SPS.get_pid(curbranch().spid)].cpid,
                              curev().iid.get_index())));
      replay = false;
      end_of_ws = prefix_idx;
      assert(conf.dpor_algorithm == Configuration::SOURCE
             || (errors.size() && errors.back()->get_location()
                 == IID<CPid>(threads[curev().iid.get_pid()].cpid,
                              curev().iid.get_index()))
             || std::all_of(threads.cbegin(), threads.cend(),
                            [](const Thread &t) { return !t.sleeping; }));
    }else if(prefix_idx + 1 != int(prefix.len()) &&
             dry_sleepers < int(prefix[prefix_idx+1].sleep.size())){
      /* Before going to the next event, dry run the threads that are
       * being put to sleep.
       */
      IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers];
      prefix[prefix_idx+1].sleep_evs.resize
        (prefix[prefix_idx+1].sleep.size());
      threads[pid].sleep_sym = &prefix[prefix_idx+1].sleep_evs[dry_sleepers];
      threads[pid].sleep_sym->clear();
      ++dry_sleepers;
      threads[pid].sleeping = true;
      //llvm::dbgs()<<"Scheduling2 "<<threads[pid].cpid<<"\n";//////////////////
      *proc = pid/2;
      *aux = pid % 2 - 1;
      *alt = 0;
      *dryrun = true;
      this->dryrun = true;
      return true;
    }else{
      /* Go to the next event. */
      assert(prefix_idx < 0 || curev().sym.size() == sym_idx
             || (errors.size() && errors.back()->get_location()
                 == IID<CPid>(threads[SPS.get_pid(curbranch().spid)].cpid,
                              curev().iid.get_index())));
      dry_sleepers = 0;
      sym_idx = 0;
      ++prefix_idx;
      IPid pid;
      if (prefix_idx < int(prefix.len())) {
        /* The event is already in prefix */
        pid = curev().iid.get_pid();
        curev().happens_after.clear();
	curev().eom_before.clear();
      } else {
        /* We are replaying from the wakeup tree */
	pid = SPS.get_pid(prefix.first_child().spid);
        prefix.enter_first_child
          (Event(IID<IPid>(pid,threads[pid].last_event_index() + 1),
                 /* Jump a few hoops to get the next Branch before
                  * calling enter_first_child() */
                 prefix.parent_at(prefix_idx).begin().branch().sym));
      }
      //llvm::dbgs()<<"Scheduling3 "<<threads[pid].cpid<<"\n";/////////////////
      *proc = pid/2;
      *aux = pid % 2 - 1;
      *alt = curbranch().alt;
      assert(threads[pid].available);
      threads[pid].event_indices.push_back(prefix_idx);
      assert(!threads[pid].sleeping);
      return true;
    }
  }

  assert(!replay);
  /* Create a new Event
   * Should we merge the last two events? */
  if(prefix.len() > 1 &&
     prefix[prefix.len()-1].iid.get_pid()
     == prefix[prefix.len()-2].iid.get_pid() &&
     !prefix[prefix.len()-1].may_conflict &&
     prefix[prefix.len()-1].sleep.empty()){
    assert(prefix.children_after(prefix.len()-1) == 0);
    assert(prefix[prefix.len()-1].wakeup.empty());
    assert(prefix_idx == prefix.len() - 1);
    assert(curev().sym.empty()); /* Would need to be copied */
    assert(curbranch().sym.empty()); /* Can't happen */
    unsigned size = curbranch().size;
    prefix.delete_last();
    --prefix_idx;
    Branch b = curbranch();
    b.size += size;
    prefix.set_last_branch(std::move(b));
    assert(int(threads[curev().iid.get_pid()].event_indices.back()) == prefix_idx + 1);
    threads[curev().iid.get_pid()].event_indices.back() = prefix_idx;
  } else {
    /* Copy symbolic events to wakeup tree */
    if (prefix.len() > 0) {
      if (!curbranch().sym.empty()) {
#ifndef NDEBUG
        sym_ty expected = curev().sym;
        if (conf.dpor_algorithm == Configuration::OBSERVERS)
          clear_observed(expected);
        assert(curbranch().sym == expected);
#endif
      } else {
        Branch b = curbranch();
        b.sym = curev().sym;
        if (conf.dpor_algorithm == Configuration::OBSERVERS)
          clear_observed(b.sym);
        for (SymEv &e : b.sym) e.purge_data();
        prefix.set_last_branch(std::move(b));
      }
    }
  }

  /* Create a new Event */
  sym_idx = 0;

  /* Find an available thread (auxiliary or real).
   *
   * Prioritize auxiliary before real, and older before younger
   * threads.
   */
  const unsigned sz = threads.size();
  unsigned p;
  for(p = 1; p < sz; p += 2){ // Loop through auxiliary threads
    if(threads[p].available && !threads[p].sleeping &&
       (conf.max_search_depth < 0 || threads[p].last_event_index() < conf.max_search_depth)){
      threads[p].event_indices.push_back(++prefix_idx);
      assert(prefix_idx == int(prefix.len()));
      IID<IPid> iid(IPid(p),threads[p].last_event_index());
      prefix.push(Branch(threads[p].spid,threads[p].last_event_index()),Event(iid));
      *proc = p/2;
      *aux = 0;
      return true;
    }
  }

  for(p = 0; p < sz; p += 2){ // Loop through real threads
    if(threads[p].available && !threads[p].sleeping &&
       (conf.max_search_depth < 0 || threads[p].last_event_index() < conf.max_search_depth)){
      threads[p].event_indices.push_back(++prefix_idx);
      assert(prefix_idx == int(prefix.len()));
      IID<IPid> iid(IPid(p),threads[p].last_event_index());
      prefix.push(Branch(threads[p].spid,threads[p].last_event_index()),Event(iid));
      *proc = p/2;
      *aux = -1;
      return true;
    }
    //else   llvm::dbgs()<<p<<" unavailable\n";///////////////////////
  }


  return false; // No available threads
}

void EventTraceBuilder::refuse_schedule(){
  assert(prefix_idx == int(prefix.len())-1);
  assert(prefix.lastbranch().size == 1);
  assert(!prefix.last().may_conflict);
  assert(prefix.last().sleep.empty());
  assert(prefix.last().wakeup.empty());
  assert(prefix.children_after(prefix_idx) == 0);
  IPid last_pid = prefix.last().iid.get_pid();
  prefix.delete_last();
  assert(int(threads[last_pid].event_indices.back()) == prefix_idx);
  threads[last_pid].event_indices.pop_back();
  --prefix_idx;
  mark_unavailable(last_pid/2,last_pid % 2 - 1);
}

void EventTraceBuilder::mark_available(int proc, int aux){
  threads[ipid(proc,aux)].available = true;
}

void EventTraceBuilder::mark_unavailable(int proc, int aux){
  threads[ipid(proc,aux)].available = false;
}

bool EventTraceBuilder::is_available(int proc, int aux){
  return threads[ipid(proc,aux)].available;
}

bool EventTraceBuilder::is_replaying() const {
  return prefix_idx < replay_point;
}

bool EventTraceBuilder::is_following_WS() const {
  return (prefix_idx+1 < int(prefix.len()));
}

void EventTraceBuilder::cancel_replay(){
  if(!replay) return;
  replay = false;
  while (prefix_idx + 1 < int(prefix.len())) prefix.delete_last();
  if (prefix.node(prefix_idx).size()) {
    prefix.enter_first_child(Event(IID<IPid>()));
    prefix.delete_last();
  }
}

void EventTraceBuilder::metadata(const llvm::MDNode *md){
  if(!dryrun && curev().md == 0){
    curev().md = md;
  }
  last_md = md;
}

bool EventTraceBuilder::sleepset_is_empty() const{
  for(unsigned i = 0; i < threads.size(); ++i){
    if(threads[i].sleeping) return false;
  }
  return true;
}

bool EventTraceBuilder::check_for_cycles(){
  /* We need vector clocks for this check */
  compute_vclocks(1);

  IID<IPid> i_iid;
  if(!has_cycle(&i_iid)) return false;

  /* Report cycle */
  {
    assert(prefix.len());
    IID<CPid> c_iid(threads[i_iid.get_pid()].cpid,i_iid.get_index());
    errors.push_back(new RobustnessError(c_iid));
  }

  return true;
}

Trace *EventTraceBuilder::get_trace() const{
  std::vector<IID<CPid> > cmp;
  SrcLocVectorBuilder cmp_md;
  std::vector<Error*> errs;
  for(unsigned i = 0; i < prefix.len(); ++i){
    cmp.push_back(IID<CPid>(threads[prefix[i].iid.get_pid()].cpid,
			    prefix[i].iid.get_index()));
    cmp_md.push_from(prefix[i].md);
  };
  for(unsigned i = 0; i < errors.size(); ++i){
    errs.push_back(errors[i]->clone());
  }
  Trace *t = new IIDSeqTrace(cmp,cmp_md.build(),errs);
  t->set_blocked(!sleepset_is_empty());
  return t;
}

bool EventTraceBuilder::reset(){
  compute_vclocks(1);
  compute_eom();
  clear_vclocks();
  compute_vclocks(2);
  remove_nonreversible_races();
  do_race_detect();
  
  if(conf.debug_print_on_reset){
    llvm::dbgs() << " === EventTraceBuilder reset ===\n";
    debug_print();
    llvm::dbgs() << " =============================\n";
  }

  if(max_branches < branches) max_branches = branches;
  branches--;
#ifndef NDEBUG
  /* The if-statement is just so we can control which test cases need to
   *  satisfy this assertion for now. Eventually, all should.
   */
  if(conf.dpor_algorithm != Configuration::SOURCE){
    check_symev_vclock_equiv();
  }
#endif

  int i;
  for(i = int(prefix.len())-1; 0 <= i; --i){
    if(prefix.children_after(i)){
      break;
    }
  }

  if(i < 0){
    /* No more branching is possible. */
    return false;
  }
  replay_point = i;

  /* Setup the new Event at prefix[i] */
  {
    uint64_t sleep_branch_trace_count =
      prefix[i].sleep_branch_trace_count + estimate_trace_count(i+1);
    Event prev_evt = std::move(prefix[i]);
    while (ssize_t(prefix.len()) > i) prefix.delete_last();

    const Branch &br = prefix.first_child();

    /* Find the index of br.pid. */
    int br_idx = 1;
    for(int j = i-1; br_idx == 1 && 0 <= j; --j){
      if(threads[prefix[j].iid.get_pid()].spid == br.spid){
        br_idx = prefix[j].iid.get_index() + prefix.branch(j).size;
      }
    }

    Event evt(IID<IPid>(SPS.get_pid(br.spid),br_idx));

    evt.sym = br.sym; /* For replay sanity assertions only */
    evt.sleep = prev_evt.sleep;
    if(br.spid != threads[prev_evt.iid.get_pid()].spid){
      if(threads[prev_evt.iid.get_pid()].handler_id != -1 &&
         prefix[i-1].iid.get_pid() != prev_evt.iid.get_pid()){
	//add into sleep tree
      }
      else evt.sleep.insert(threads[prev_evt.iid.get_pid()].spid);
    }
    evt.sleep_branch_trace_count = sleep_branch_trace_count;

    prefix.enter_first_child(std::move(evt));
  }

  CPS = CPidSystem();
  threads.clear();
  threads.push_back(Thread(CPid(),-1));
  threads.push_back(Thread(CPS.new_aux(CPid()),-1));
  threads[1].available = false; // Store buffer is empty.
  threads[0].spid = 0;
  mutexes.clear();
  cond_vars.clear();
  mem.clear();
  last_full_memory_conflict = -1;
  prefix_idx = -1;
  dryrun = false;
  replay = true;
  dry_sleepers = 0;
  last_md = 0;
  reset_cond_branch_log();
  has_vclocks = false;

  return true;
}

IID<CPid> EventTraceBuilder::get_iid() const{
  IPid pid = curev().iid.get_pid();
  int idx = curev().iid.get_index();
  return IID<CPid>(threads[pid].cpid,idx);
}

int EventTraceBuilder::get_spid(int pid){
  return threads[pid*2].spid;
} 

static std::string rpad(std::string s, int n){
  while(int(s.size()) < n) s += " ";
  return s;
}

std::string EventTraceBuilder::iid_string(std::size_t pos) const{
  return iid_string(prefix.branch(pos), prefix[pos].iid.get_index());
}

std::string EventTraceBuilder::iid_string(const Branch &branch, int index) const{
  std::stringstream ss;
  ss << "(" << threads[SPS.get_pid(branch.spid)].cpid << "," << index;
  if(branch.size > 1){
    ss << "-" << index + branch.size - 1;
  }
  ss << ")";
  if(branch.alt != 0){
    ss << "-alt:" << branch.alt;
  }
  return ss.str();
}

static std::string
str_join(const std::vector<std::string> &vec, const std::string &sep) {
  std::string res;
  for (auto it = vec.begin(); it != vec.end(); ++it) {
    if (it != vec.begin()) res += sep;
    res += *it;
  }
  return res;
}

std::string EventTraceBuilder::oslp_string(const struct obs_sleep &os) const {
  std::vector<std::string> elems;
  auto pid_str = [this](IPid p) { return threads[p].cpid.to_string(); };
  for (const auto &sleeper : os.sleep) {
    elems.push_back(threads[SPS.get_pid(sleeper.spid)].cpid.to_string());
    if (sleeper.not_if_read) {
      elems.back() += "/" + sleeper.not_if_read->to_string(pid_str);
    }
  }
  for (const SymAddrSize &sas : os.must_read) {
    elems.push_back(sas.to_string(pid_str));
  }
  return "{" + str_join(elems, ",") + "}";
}

/* For debug-printing the wakeup tree; adds a node and its children to lines */
void EventTraceBuilder::wut_string_add_node
(std::vector<std::string> &lines, std::vector<int> &iid_map,
 unsigned line, Branch branch, WakeupTreeRef<Branch> node) const{
  unsigned offset = 2 + ((lines.size() < line)?0:lines[line].size());

  std::vector<std::pair<Branch,WakeupTreeRef<Branch>>> nodes({{branch,node}});
  iid_map_step(iid_map, branch);
  unsigned l = line;
  WakeupTreeRef<Branch> n = node;
  Branch b = branch;
  while (n.size()) {
    b = n.begin().branch();
    n = n.begin().node();
    ++l;
    nodes.push_back({b,n});
    iid_map_step(iid_map, b);
    if (l < lines.size()) offset = std::max(offset, unsigned(lines[l].size()));
  }
  if (lines.size() < l+1) lines.resize(l+1, "");
  /* First node needs different padding, so we do it here */
  lines[line] += " ";
  while(lines[line].size() < offset) lines[line] += "-";

  while(nodes.size()) {
    l = line+nodes.size()-1;
    b = nodes.back().first;
    n = nodes.back().second;
    for (auto ci = n.begin(); ci != n.end(); ++ci) {
      if (ci == n.begin()) continue;
      wut_string_add_node(lines, iid_map, l+1, ci.branch(), ci.node());
    }
    iid_map_step_rev(iid_map, b);
    while(lines[l].size() < offset) lines[l] += " ";
    lines[l] += " " + iid_string(b, iid_map[b.spid]);
    nodes.pop_back();
  }
}

static std::string events_to_string(const llvm::SmallVectorImpl<SymEv> &e) {
  if (e.size() == 0) return "None()";
  std::string res;
  for (unsigned i = 0; i < e.size(); ++i) {
    res += e[i].to_string();
    if (i != e.size()-1) res += ", ";
  }
  return res;
}

#ifndef NDEBUG
void EventTraceBuilder::check_symev_vclock_equiv() const {
  /* Check for SymEv<->VClock equivalence
   * SymEv considers that event i happens after event j iff there is a
   * subsequence s of i..j including i and j s.t.
   *   forall 0 <= k < len(s)-1. do_events_conflict(s[k], s[k+1])
   * As checking all possible subseqences is exponential, we instead rely on
   * the fact that we've already verified the SymEv<->VClock equivalence of
   * any pair in 0..i-1. Thus, it is sufficient to check whether i has a
   * conflict with some event k which has a vector clock strictly greater than
   * j.
   */
  /* The frontier is the set of events such that e is the first event of pid
   * that happen after the event.
   */
  std::vector<unsigned> frontier;
  for (unsigned i = 0; i < prefix.len(); ++i) {
    const Event &e = prefix[i];
    const IPid pid = e.iid.get_pid();
    const Event *prev
      = (e.iid.get_index() == 1 ? nullptr
         : &prefix[find_process_event(pid, e.iid.get_index()-1)]);
    if (i == prefix.len() - 1 && errors.size() &&
        errors.back()->get_location()
        == IID<CPid>(threads[pid].cpid, e.iid.get_index())) {
      /* Ignore dependency differences with the errored event in aborted
       * executions
       */
      break;
    }
    for (unsigned j = i-1; j != unsigned(-1); --j) {
      bool iafterj = false;
      if (prefix[j].iid.get_pid() == pid
          || do_events_conflict(i,j)) {
        iafterj = true;
        if (!prev || !prefix[j].clock.leq(prev->clock)) {
          frontier.push_back(j);
        }
      } else if (prev && prefix[j].clock.leq(prev->clock)) {
        iafterj = true;
      } else {
        for (unsigned k : frontier) {
          if (prefix[j].clock.leq(prefix[k].clock)) {
            iafterj = true;
            break;
          }
        }
      }

      if (iafterj != prefix[j].clock.leq(e.clock)) {
        if (iafterj) {
          llvm::dbgs() << "SymEv thinks " << i << " happens after " << j
                       << " but vclock does not\n";
        } else {
          llvm::dbgs() << "VClock thinks " << i << " happens after " << j
                       << " but SymEv does not\n";
        }
        int ix_offs = 0;
        int iid_offs = 0;
        int clock_offs = 0;
        for(unsigned k = 0; k < prefix.len(); ++k){
          IPid ipid = prefix[k].iid.get_pid();
          ix_offs = std::max(ix_offs,int(std::to_string(k).size()));
          iid_offs = std::max(iid_offs,2*ipid+int(iid_string(k).size()));
          clock_offs = std::max(clock_offs,int(prefix[k].clock.to_string().size()));
        }

        for(unsigned k = 0; k < prefix.len(); ++k){
          IPid ipid = prefix[k].iid.get_pid();
          llvm::dbgs() << rpad("",ix_offs-int(std::to_string(k).size()))
                       << (k == i || k == j ? ANSIRed : "") << k
                       << (k == i || k == j ? ANSIRst : "")
                       << ":" << rpad("",2+ipid*2)
                       << rpad(iid_string(k),iid_offs-ipid*2)
                       << " " << rpad(prefix[k].clock.to_string(),clock_offs)
                       << " " << events_to_string(prefix[k].sym)
                       << "\n";
        }
        if(errors.size()){
          llvm::dbgs() << "Errors:\n";
          for(unsigned k = 0; k < errors.size(); ++k){
            llvm::dbgs() << "  Error #" << k+1 << ": "
                         << errors[k]->to_string() << "\n";
          }
        }
      }
      assert(iafterj == prefix[j].clock.leq(e.clock));
    }

    /* Cleanup */
    frontier.clear();
  }
}
#endif /* !defined(NDEBUG) */

void EventTraceBuilder::debug_print() const {
  llvm::dbgs() << "EventTraceBuilder (debug print):\n";
  int iid_offs = 0;
  int symev_offs = 0;
  std::vector<std::string> lines;
  struct obs_sleep sleep_set;

  for(unsigned i = 0; i < prefix.len(); ++i){
    IPid ipid = prefix[i].iid.get_pid();
    iid_offs = std::max(iid_offs,2*ipid+int(iid_string(i).size()));
    symev_offs = std::max(symev_offs,
                          int(events_to_string(prefix[i].sym).size()));
    obs_sleep_add(sleep_set, prefix[i]);
    lines.push_back(" SLP:" + oslp_string(sleep_set));
    obs_sleep_wake(sleep_set, threads[ipid].spid, prefix[i].sym);
  }

  /* Add wakeup tree */
  std::vector<int> iid_map = iid_map_at(prefix.len());
  for(int i = prefix.len()-1; 0 <= i; --i){
    auto node = prefix.parent_at(i);
    iid_map_step_rev(iid_map, prefix.branch(i));
    for (auto it = node.begin(); it != node.end(); ++it) {
      Branch b = it.branch();
      if (b == prefix.branch(i)) continue; /* Only print others */
      wut_string_add_node(lines, iid_map, i, it.branch(), it.node());
    }
  }

  for(unsigned i = 0; i < prefix.len(); ++i){
    IPid ipid = prefix[i].iid.get_pid();
    llvm::dbgs() << rpad("",2+ipid*2)
                 << rpad(iid_string(i),iid_offs-ipid*2)
      //<< rpad(events_to_string(prefix[i].sym), 40)///////////////////////
                 << " " << rpad(events_to_string(prefix[i].sym),symev_offs)
                 << lines[i] << "\n";
  }
  for (unsigned i = prefix.len(); i < lines.size(); ++i){
    llvm::dbgs() << std::string(2+iid_offs + 1+symev_offs, ' ') << lines[i] << "\n";
  }
  if(errors.size()){
    llvm::dbgs() << "Errors:\n";
    for(unsigned i = 0; i < errors.size(); ++i){
      llvm::dbgs() << "  Error #" << i+1 << ": "
                   << errors[i]->to_string() << "\n";
    }
  }
}

bool EventTraceBuilder::spawn(){
  IPid parent_ipid = curev().iid.get_pid();
  CPid child_cpid = CPS.spawn(threads[parent_ipid].cpid);
  SPS.set_spid_map(child_cpid,threads.size());
  /* TODO: First event of thread happens before parents spawn */
  threads.push_back(Thread(child_cpid,prefix_idx));
  threads.back().spid = SPS.get_spid(child_cpid);
  threads.push_back(Thread(CPS.new_aux(child_cpid),prefix_idx));
  threads.back().spid = SPS.get_spid(child_cpid);
  threads.back().available = false; // Empty store buffer
  return record_symbolic(SymEv::Spawn(SPS.get_spid(child_cpid)));
}
//TODO: Reuse code of spawn to do create()
void EventTraceBuilder::create(){
  IPid parent_ipid = curev().iid.get_pid();
  CPid child_cpid = CPS.spawn(threads[parent_ipid].cpid);
  SPS.set_spid_map(child_cpid,threads.size());
  /* TODO: First event of thread happens before parents spawn */
  threads.push_back(Thread(child_cpid,prefix_idx));
  threads.back().spid = SPS.get_spid(child_cpid);
  threads.back().available = false;
  threads.push_back(Thread(CPS.new_aux(child_cpid),prefix_idx));
  threads.back().spid = SPS.get_spid(child_cpid);
  threads.back().available = false; // Empty store buffer
}

bool EventTraceBuilder::start(int pid){
  if(threads.size() <= pid*2){
    llvm::dbgs() << "Error:Thread not found while trying to start\n";
    return false;
  }
  if(threads[pid*2].available == true){
    llvm::dbgs() << "Error:Thread already started\n";
  }
  if(prefix_idx > threads[pid*2].spawn_event)
    add_happens_after(prefix_idx, threads[pid*2].spawn_event);
  threads[pid*2].spawn_event = prefix_idx;
  threads[pid*2+1].spawn_event = prefix_idx;
  threads[pid*2].available = true; // Empty store buffer
  return record_symbolic(SymEv::Spawn(threads[pid*2].spid));
}

bool EventTraceBuilder::post(const int tgt_th) {
  IPid tpid = tgt_th*2;
  if(threads.size() <= tpid) {
    llvm::dbgs() << "Error: Cannot post to " << tgt_th
		 << "because it doesn't exist\n";
    return false;
  }

  IPid ipid = curev().iid.get_pid();
  assert(0 <= tpid && tpid<threads.size());
  create();
  threads[threads.size()-2].handler_id = tpid;
  threads[threads.size()-1].handler_id = tpid;
  return record_symbolic(SymEv::Post(threads[threads.size()-2].spid));
}

bool EventTraceBuilder::store(const SymData &sd){
  if(dryrun) return true;
  curev().may_conflict = true; /* prefix_idx might become bad otherwise */
  IPid ipid = curev().iid.get_pid();
  threads[ipid].store_buffer.push_back(PendingStore(sd.get_ref(),prefix_idx,last_md));
  threads[ipid+1].available = true;
  return true;
}

bool EventTraceBuilder::atomic_store(const SymData &sd){
  if (conf.dpor_algorithm == Configuration::OBSERVERS) {
    if (!record_symbolic(SymEv::UnobsStore(sd))) return false;
  } else {
    if (!record_symbolic(SymEv::Store(sd))) return false;
  }
  do_atomic_store(sd);
  return true;
}

static bool symev_is_store(const SymEv &e) {
  return e.kind == SymEv::UNOBS_STORE || e.kind == SymEv::STORE;
}

static bool symev_does_store(const SymEv &e) {
  return e.kind == SymEv::UNOBS_STORE || e.kind == SymEv::STORE
    || e.kind == SymEv::CMPXHG;
}

static SymAddrSize sym_get_last_write(const sym_ty &sym, SymAddr addr){
  for (auto it = sym.end(); it != sym.begin();){
    const SymEv &e = *(--it);
    if (symev_does_store(e) && e.addr().includes(addr)) return e.addr();
  }
  assert(false && "No write touching addr found");
  abort();
}

void EventTraceBuilder::do_atomic_store(const SymData &sd){
  const SymAddrSize &ml = sd.get_ref();
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    VecSet<SymAddr> &A = threads[pid].sleep_accesses_w;
    for(SymAddr b : ml){
      A.insert(b);
    }
    return;
  }
  IPid ipid = curev().iid.get_pid();
  bool is_update = ipid % 2;

  IPid uipid = ipid; // ID of the thread changing the memory
  IPid tipid = is_update ? ipid-1 : ipid; // ID of the (real) thread that issued the store

  if(is_update){ // Add the clock of the store instruction
    assert(threads[tipid].store_buffer.size());
    const PendingStore &pst = threads[tipid].store_buffer.front();
    assert(pst.store_event != (unsigned)prefix_idx);
    add_happens_after(prefix_idx, pst.store_event);
    curev().origin_iid = prefix[pst.store_event].iid;
    curev().md = pst.md;
  }else{ // Add the clock of the auxiliary thread (because of fence semantics)
    assert(threads[tipid].store_buffer.empty());
    add_happens_after_thread(prefix_idx, tipid+1);
  }

  VecSet<int> seen_accesses;

  /* See previous updates reads to ml */
  for(SymAddr b : ml){
    ByteInfo &bi = mem[b];
    int lu = bi.last_update;
    assert(lu < int(prefix.len()));
    if(0 <= lu){
      IPid lu_tipid = 2*(prefix[lu].iid.get_pid() / 2);
      if(lu_tipid != tipid){
        if(conf.dpor_algorithm == Configuration::OBSERVERS){
          SymAddrSize lu_addr = sym_get_last_write(prefix[lu].sym, b);
          if (lu_addr != ml) {
            /* When there is "partial overlap", observers requires
             * writes to be unconditionally racing
             */
            seen_accesses.insert(bi.last_update);
            bi.unordered_updates.clear();
          }
        }else{
          seen_accesses.insert(bi.last_update);
        }
      }
    }
    for(int i : bi.last_read){
      if(0 <= i && prefix[i].iid.get_pid() != tipid) seen_accesses.insert(i);
    }

    /* Register in memory */
    if (conf.dpor_algorithm == Configuration::OBSERVERS) {
      bi.unordered_updates.insert_geq(prefix_idx);
    }
    bi.last_update = prefix_idx;
    bi.last_update_ml = ml;
    if(is_update && threads[tipid].store_buffer.front().last_rowe >= 0){
      bi.last_read[tipid/2] = threads[tipid].store_buffer.front().last_rowe;
    }
    wakeup(Access::W,b);
  }

  if(is_update){ /* Remove pending store from buffer */
    for(unsigned i = 0; i < threads[tipid].store_buffer.size()-1; ++i){
      threads[tipid].store_buffer[i] = threads[tipid].store_buffer[i+1];
    }
    threads[tipid].store_buffer.pop_back();
    if(threads[tipid].store_buffer.empty()){
      threads[uipid].available = false;
    }
  }

  seen_accesses.insert(last_full_memory_conflict);

  see_events(seen_accesses);
}

bool EventTraceBuilder::load(const SymAddrSize &ml){
  if (!record_symbolic(SymEv::Load(ml))) return false;
  do_load(ml);
  return true;
}

void EventTraceBuilder::do_load(const SymAddrSize &ml){
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    VecSet<SymAddr> &A = threads[pid].sleep_accesses_r;
    for(SymAddr b : ml){
      A.insert(b);
    }
    return;
  }
  IPid ipid = curev().iid.get_pid();

  /* Check if this is a ROWE */
  for(int i = int(threads[ipid].store_buffer.size())-1; 0 <= i; --i){
    if(threads[ipid].store_buffer[i].ml.addr == ml.addr){
      /* ROWE */
      threads[ipid].store_buffer[i].last_rowe = prefix_idx;
      return;
    }
  }

  /* Load from memory */
  VecSet<int> seen_accesses;

  /* See all updates to the read bytes. */
  for(SymAddr b : ml){
    int lu = mem[b].last_update;
    const SymAddrSize &lu_ml = mem[b].last_update_ml;
    if(0 <= lu){
      IPid lu_tipid = prefix[lu].iid.get_pid() & ~0x1;
      if(lu_tipid == ipid && ml != lu_ml && lu != prefix_idx){
        add_happens_after(prefix_idx, lu);
      }
    }
    do_load(mem[b]);

    /* Register load in memory */
    mem[b].last_read[ipid/2] = prefix_idx;
    wakeup(Access::R,b);
  }

  seen_accesses.insert(last_full_memory_conflict);

  see_events(seen_accesses);
}

bool EventTraceBuilder::compare_exchange
(const SymData &sd, const SymData::block_type expected, bool success){
  if(success){
    if (!record_symbolic(SymEv::CmpXhg(sd, expected))) return false;
    do_load(sd.get_ref());
    do_atomic_store(sd);
  }else{
    if (!record_symbolic(SymEv::CmpXhgFail(sd, expected))) return false;
    do_load(sd.get_ref());
  }
  return true;
}

bool EventTraceBuilder::full_memory_conflict(){
  if (!record_symbolic(SymEv::Fullmem())) return false;
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_full_memory_conflict = true;
    return true;
  }

  /* See all pervious memory accesses */
  VecSet<int> seen_accesses;
  for(auto it = mem.begin(); it != mem.end(); ++it){
    do_load(it->second);
    for(int i : it->second.last_read){
      seen_accesses.insert(i);
    }
  }
  for(auto it = mutexes.begin(); it != mutexes.end(); ++it){
    seen_accesses.insert(it->second.last_access);
  }
  seen_accesses.insert(last_full_memory_conflict);
  last_full_memory_conflict = prefix_idx;

  wakeup(Access::W_ALL_MEMORY,{SymMBlock::Global(0),0});

  /* No later access can have a conflict with any earlier access */
  mem.clear();

  see_events(seen_accesses);
  return true;
}

void EventTraceBuilder::do_load(ByteInfo &m){
  IPid ipid = curev().iid.get_pid();
  VecSet<int> seen_accesses;
  VecSet<std::pair<int,int>> seen_pairs;

  int lu = m.last_update;
  const SymAddrSize &lu_ml = m.last_update_ml;
  if(0 <= lu){
    IPid lu_tipid = prefix[lu].iid.get_pid() & ~0x1;
    if(lu_tipid != ipid){
      seen_accesses.insert(lu);
    }
    if (conf.dpor_algorithm == Configuration::OBSERVERS) {
      /* Update last_update to be an observed store */
      for (auto it = prefix[lu].sym.end();;){
        assert(it != prefix[lu].sym.begin());
        --it;
        if((it->kind == SymEv::STORE || it->kind == SymEv::CMPXHG)
           && it->addr() == lu_ml) break;
        if (it->kind == SymEv::UNOBS_STORE && it->addr() == lu_ml) {
          *it = SymEv::Store(it->data());
          break;
        }
      }
      /* Add races */
      for (int u : m.unordered_updates){
        if (prefix[lu].iid != prefix[u].iid) {
          seen_pairs.insert(std::pair<int,int>(u, lu));
        }
      }
      m.unordered_updates.clear();
    }
  }
  assert(m.unordered_updates.size() == 0);
  see_events(seen_accesses);
  see_event_pairs(seen_pairs);
}

bool EventTraceBuilder::fence(){
  if(dryrun) return true;
  IPid ipid = curev().iid.get_pid();
  assert(ipid % 2 == 0);
  assert(threads[ipid].store_buffer.empty());
  add_happens_after_thread(prefix_idx, ipid+1);
  return true;
}

bool EventTraceBuilder::join(int tgt_proc){
  if (!record_symbolic(SymEv::Join(threads[tgt_proc].spid)))
    return false;
  if(dryrun) return true;
  assert(threads[tgt_proc*2].store_buffer.empty());
  add_happens_after_thread(prefix_idx, tgt_proc*2);
  add_happens_after_thread(prefix_idx, tgt_proc*2+1);
  return true;
}

bool EventTraceBuilder::mutex_lock(const SymAddrSize &ml){
  if (!record_symbolic(SymEv::MLock(ml))) return false;
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.addr);
    return true;
  }
  if (!fence()) return false;
  if(!conf.mutex_require_init && !mutexes.count(ml.addr)){
    // Assume static initialization
    mutexes[ml.addr] = Mutex();
  }
  wakeup(Access::W,ml.addr);

  Mutex &mutex = mutexes[ml.addr];

  if(mutex.last_lock < 0){
    /* No previous lock */
    see_events({mutex.last_access,last_full_memory_conflict});
  }else{
    add_lock_suc_race(mutex.last_lock, mutex.last_access);
    see_events({last_full_memory_conflict});
  }

  mutex.last_lock = mutex.last_access = prefix_idx;
  mutex.locked = true;
  return true;
}

bool EventTraceBuilder::mutex_lock_fail(const SymAddrSize &ml){
  assert(!dryrun);
  if(!conf.mutex_require_init && !mutexes.count(ml.addr)){
    // Assume static initialization
    mutexes[ml.addr] = Mutex();
  }
  assert(mutexes.count(ml.addr));
  Mutex &mutex = mutexes[ml.addr];
  assert(0 <= mutex.last_lock);
  add_lock_fail_race(mutex, mutex.last_lock);

  if(0 <= last_full_memory_conflict){
    add_lock_fail_race(mutex, last_full_memory_conflict);
  }
  return true;
}

bool EventTraceBuilder::mutex_trylock(const SymAddrSize &ml){
  if (!record_symbolic(SymEv::MLock(ml))) return false;
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.addr);
    return true;
  }
  if (!fence()) return false;
  if(!conf.mutex_require_init && !mutexes.count(ml.addr)){
    // Assume static initialization
    mutexes[ml.addr] = Mutex();
  }
  assert(mutexes.count(ml.addr));
  wakeup(Access::W,ml.addr);
  Mutex &mutex = mutexes[ml.addr];
  see_events({mutex.last_access,last_full_memory_conflict});

  mutex.last_access = prefix_idx;
  if(!mutex.locked){ // Mutex is free
    mutex.last_lock = prefix_idx;
    mutex.locked = true;
  }
  return true;
}

bool EventTraceBuilder::mutex_unlock(const SymAddrSize &ml){
  if (!record_symbolic(SymEv::MUnlock(ml))) return false;
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.addr);
    return true;
  }
  if (!fence()) return false;
  if(!conf.mutex_require_init && !mutexes.count(ml.addr)){
    // Assume static initialization
    mutexes[ml.addr] = Mutex();
  }
  assert(mutexes.count(ml.addr));
  Mutex &mutex = mutexes[ml.addr];
  wakeup(Access::W,ml.addr);
  assert(0 <= mutex.last_access);

  see_events({mutex.last_access,last_full_memory_conflict});

  mutex.last_access = prefix_idx;
  mutex.locked = false;
  return true;
}

bool EventTraceBuilder::mutex_init(const SymAddrSize &ml){
  if (!record_symbolic(SymEv::MInit(ml))) return false;
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.addr);
    return true;
  }
  if (!fence()) return false;
  Mutex &mutex = mutexes[ml.addr];
  see_events({mutex.last_access, last_full_memory_conflict});

  mutex.last_access = prefix_idx;
  return true;
}

bool EventTraceBuilder::mutex_destroy(const SymAddrSize &ml){
  if (!record_symbolic(SymEv::MDelete(ml))) return false;
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.addr);
    return true;
  }
  if (!fence()) return false;
  if(!conf.mutex_require_init && !mutexes.count(ml.addr)){
    // Assume static initialization
    mutexes[ml.addr] = Mutex();
  }
  assert(mutexes.count(ml.addr));
  Mutex &mutex = mutexes[ml.addr];
  wakeup(Access::W,ml.addr);

  see_events({mutex.last_access,last_full_memory_conflict});

  mutexes.erase(ml.addr);
  return true;
}

bool EventTraceBuilder::cond_init(const SymAddrSize &ml){
  if (!record_symbolic(SymEv::CInit(ml))) return false;
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.addr);
    return true;
  }
  if (!fence()) return false;
  if(cond_vars.count(ml.addr)){
    pthreads_error("Condition variable initiated twice.");
    return false;
  }
  cond_vars[ml.addr] = CondVar(prefix_idx);
  see_events({last_full_memory_conflict});
  return true;
}

bool EventTraceBuilder::cond_signal(const SymAddrSize &ml){
  if (!record_symbolic(SymEv::CSignal(ml))) return false;
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.addr);
    return true;
  }
  if (!fence()) return false;
  wakeup(Access::W,ml.addr);
  
  auto it = cond_vars.find(ml.addr);
  if(it == cond_vars.end()){
    pthreads_error("cond_signal called with uninitialized condition variable.");
    return false;
  }
  CondVar &cond_var = it->second;
  VecSet<int> seen_events = {last_full_memory_conflict};
  if(cond_var.waiters.size() > 1){
    if (!register_alternatives(cond_var.waiters.size())) return false;
  }
  assert(0 <= curbranch().alt);
  assert(cond_var.waiters.empty() || curbranch().alt < int(cond_var.waiters.size()));
  if(cond_var.waiters.size()){
    /* Wake up the alt:th waiter. */
    int i = cond_var.waiters[curbranch().alt];
    assert(0 <= i && i < prefix_idx);
    IPid ipid = prefix[i].iid.get_pid();
    assert(!threads[ipid].available);
    threads[ipid].available = true;
    seen_events.insert(i);

    /* Remove waiter from cond_var.waiters */
    for(int j = curbranch().alt; j < int(cond_var.waiters.size())-1; ++j){
      cond_var.waiters[j] = cond_var.waiters[j+1];
    }
    cond_var.waiters.pop_back();
  }
  cond_var.last_signal = prefix_idx;

  see_events(seen_events);

  return true;
}

bool EventTraceBuilder::cond_broadcast(const SymAddrSize &ml){
  if (!record_symbolic(SymEv::CBrdcst(ml))) return false;
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.addr);
    return true;
  }
  if (!fence()) return false;
  wakeup(Access::W,ml.addr);

  auto it = cond_vars.find(ml.addr);
  if(it == cond_vars.end()){
    pthreads_error("cond_broadcast called with uninitialized condition variable.");
    return false;
  }
  CondVar &cond_var = it->second;
  VecSet<int> seen_events = {last_full_memory_conflict};
  for(int i : cond_var.waiters){
    assert(0 <= i && i < prefix_idx);
    IPid ipid = prefix[i].iid.get_pid();
    assert(!threads[ipid].available);
    threads[ipid].available = true;
    seen_events.insert(i);
  }
  cond_var.waiters.clear();
  cond_var.last_signal = prefix_idx;

  see_events(seen_events);

  return true;
}

bool EventTraceBuilder::cond_wait(const SymAddrSize &cond_ml, const SymAddrSize &mutex_ml){
  {
    auto it = mutexes.find(mutex_ml.addr);
    if(!dryrun && it == mutexes.end()){
      if(conf.mutex_require_init){
        pthreads_error("cond_wait called with uninitialized mutex object.");
      }else{
        pthreads_error("cond_wait called with unlocked mutex object.");
      }
      return false;
    }
    Mutex &mtx = it->second;
    if(!dryrun && (mtx.last_lock < 0 || prefix[mtx.last_lock].iid.get_pid() != curev().iid.get_pid())){
      pthreads_error("cond_wait called with mutex which is not locked by the same thread.");
      return false;
    }
  }

  if (!mutex_unlock(mutex_ml)) return false;
  if (!record_symbolic(SymEv::CWait(cond_ml))) return false;
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_r.insert(cond_ml.addr);
    return true;
  }
  if (!fence()) return false;
  wakeup(Access::R,cond_ml.addr);

  IPid pid = curev().iid.get_pid();

  auto it = cond_vars.find(cond_ml.addr);
  if(it == cond_vars.end()){
    pthreads_error("cond_wait called with uninitialized condition variable.");
    return false;
  }
  it->second.waiters.push_back(prefix_idx);
  threads[pid].available = false;

  see_events({last_full_memory_conflict,it->second.last_signal});

  return true;
}

bool EventTraceBuilder::cond_awake(const SymAddrSize &cond_ml, const SymAddrSize &mutex_ml){
  if (!dryrun){
    assert(cond_vars.count(cond_ml.addr));
    CondVar &cond_var = cond_vars[cond_ml.addr];
    add_happens_after(prefix_idx, cond_var.last_signal);
  }

  if (!mutex_lock(mutex_ml)) return false;
  if (!record_symbolic(SymEv::CAwake(cond_ml))) return false;
  if(dryrun){
    return true;
  }

  return true;
}

int EventTraceBuilder::cond_destroy(const SymAddrSize &ml){
  const int err = (EBUSY == 1) ? 2 : 1; // Chose an error value different from EBUSY

  if (!record_symbolic(SymEv::CDelete(ml))) return err;
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.addr);
    return 0;
  }
  if (!fence()) return err;

  wakeup(Access::W,ml.addr);

  auto it = cond_vars.find(ml.addr);
  if(it == cond_vars.end()){
    pthreads_error("cond_destroy called on uninitialized condition variable.");
    return err;
  }
  CondVar &cond_var = it->second;
  VecSet<int> seen_events = {cond_var.last_signal,last_full_memory_conflict};
  for(int i : cond_var.waiters) seen_events.insert(i);
  see_events(seen_events);

  int rv = cond_var.waiters.size() ? EBUSY : 0;
  cond_vars.erase(ml.addr);
  return rv;
}

bool EventTraceBuilder::register_alternatives(int alt_count){
  if (!record_symbolic(SymEv::Nondet(alt_count))) return false;
  if(curbranch().alt == 0) {
    for(int i = curbranch().alt+1; i < alt_count; ++i){
      curev().races.push_back(Race::Nondet(prefix_idx, i));
    }
  }
  return true;
}

void EventTraceBuilder::obs_sleep_add(struct obs_sleep &sleep,
                                    const Event &e) const{
  for (int k = 0; k < e.sleep.size(); ++k){
    sleep.sleep.push_back({e.sleep[k], &e.sleep_evs[k], nullptr});
  }
}

/* Efficient unordered set delete */
template <typename T> static inline
void unordered_vector_delete(std::vector<T> &vec, std::size_t pos) {
  assert(pos < vec.size());
  if (pos+1 != vec.size())
    vec[pos] = std::move(vec.back());
  vec.pop_back();
}

void
EventTraceBuilder::obs_sleep_wake(struct obs_sleep &sleep, const Event &e) const{
  if (conf.dpor_algorithm != Configuration::OBSERVERS) {
    if (e.wakeup.size()) {
      for (unsigned i = 0; i < sleep.sleep.size();) {
        if (e.wakeup.count(sleep.sleep[i].spid)) {
          unordered_vector_delete(sleep.sleep, i);
        } else {
          ++i;
        }
      }
    }
  } else {
    sym_ty sym = e.sym;
    /* A tricky part to this is that we must clear observers from the events
     * we use to wake */
    clear_observed(sym);
#ifndef NDEBUG
    obs_wake_res res =
#endif
      obs_sleep_wake(sleep, threads[e.iid.get_pid()].spid, sym);
    assert(res != obs_wake_res::BLOCK);
  }
}

static bool symev_does_load(const SymEv &e) {
  return e.kind == SymEv::LOAD || e.kind == SymEv::CMPXHG
    || e.kind == SymEv::CMPXHGFAIL || e.kind == SymEv::FULLMEM;
}

EventTraceBuilder::obs_wake_res
EventTraceBuilder::obs_sleep_wake(struct obs_sleep &sleep,
                                IPid p, const sym_ty &sym) const{

  if (conf.dpor_algorithm == Configuration::OBSERVERS) {
    for (const SymEv &e : sym) {
      /* Now check for readers */
      if (e.kind == SymEv::FULLMEM) {
        /* Reads all; observes all */
        sleep.must_read.clear();
      } else if (symev_does_load(e)) {
        const SymAddrSize &esas = e.addr();
        for (int i = 0; i < int(sleep.must_read.size());) {
          if (sleep.must_read[i].overlaps(esas)) {
            unordered_vector_delete(sleep.must_read, i);
          } else {
            ++i;
          }
        }
      }
      if (symev_is_store(e)) {
        /* Now check for shadowing of needed observations */
        const SymAddrSize &esas = e.addr();
        if (std::any_of(sleep.must_read.begin(), sleep.must_read.end(),
                        [&esas](const SymAddrSize &ssas) {
                          return ssas.subsetof(esas);
                        })) {
          return obs_wake_res::BLOCK;
        }
        /* Now handle write-write races by moving the sleepers to sleep_if */
        for (auto it = sleep.sleep.begin(); it != sleep.sleep.end(); ++it) {
          if (std::any_of(it->sym->begin(), it->sym->end(),
                          [&esas](const SymEv &f) {
                            return symev_is_store(f) && f.addr() == esas;
                          })) {
            assert(!it->not_if_read || *it->not_if_read == esas);
            it->not_if_read = esas;
          }
        }
      }
    }
  }

  for (unsigned i = 0; i < sleep.sleep.size();) {
    const auto &s = sleep.sleep[i];
    if (s.spid == p) {
      if (s.not_if_read) {
        sleep.must_read.push_back(*s.not_if_read);
        unordered_vector_delete(sleep.sleep, i);
      } else {
        return obs_wake_res::BLOCK;
      }
    } else if (do_events_conflict(p, sym, s.spid, *s.sym)){
      unordered_vector_delete(sleep.sleep, i);
    } else {
      ++i;
    }
  }

  /* Check if the sleep set became empty */
  if (sleep.sleep.empty() && sleep.must_read.empty()) {
    return obs_wake_res::CLEAR;
  } else {
    return obs_wake_res::CONTINUE;
  }
}

static void clear_observed(SymEv &e){
  if (e.kind == SymEv::STORE){
    e.set_observed(false);
  }
}

static void clear_observed(sym_ty &syms){
  for (SymEv &e : syms){
    clear_observed(e);
  }
}

bool EventTraceBuilder::
sequence_clears_sleep(const std::vector<Branch> &seq,
                      const struct obs_sleep &sleep_const) const{
  /* We need a writable copy */
  struct obs_sleep isleep = sleep_const;
  obs_wake_res state = obs_wake_res::CONTINUE;
  for (auto it = seq.cbegin(); state == obs_wake_res::CONTINUE
         && it != seq.cend(); ++it) {
    state = obs_sleep_wake(isleep, it->spid, it->sym);
  }
  /* Redundant */
  return (state == obs_wake_res::CLEAR);
}

template <class Iter>
static void rev_recompute_data
(SymData &data, VecSet<SymAddr> &needed, Iter end, Iter begin){
  for (auto pi = end; !needed.empty() && (pi != begin);){
    const SymEv &p = *(--pi);
    switch(p.kind){
    case SymEv::STORE:
    case SymEv::UNOBS_STORE:
    case SymEv::CMPXHG:
      if (data.get_ref().overlaps(p.addr())) {
        for (SymAddr a : p.addr()) {
          if (needed.erase(a)) {
            data[a] = p.data()[a];
          }
        }
      }
      break;
    default:
      break;
    }
  }
}

void EventTraceBuilder::recompute_cmpxhg_success
(sym_ty &es, const std::vector<Branch> &v, int i) const {
  for (auto ei = es.begin(); ei != es.end(); ++ei) {
    SymEv &e = *ei;
    if (e.kind == SymEv::CMPXHG || e.kind == SymEv::CMPXHGFAIL) {
      SymData data(e.addr(), e.addr().size);
      VecSet<SymAddr> needed(e.addr().begin(), e.addr().end());
      std::memset(data.get_block(), 0, e.addr().size);

      /* Scan in reverse for data */
      rev_recompute_data(data, needed, ei, es.begin());
      for (auto vi = v.end(); !needed.empty() && (vi != v.begin());){
        const Branch &vb = *(--vi);
        rev_recompute_data(data, needed, vb.sym.end(), vb.sym.begin());
      }
      for (int k = i-1; !needed.empty() && (k >= 0); --k){
        const sym_ty &ps = prefix[k].sym;
        rev_recompute_data(data, needed, ps.end(), ps.begin());
      }

      /* If needed isn't empty then the program reads uninitialised data. */
      // assert(needed.empty());

      bool will_succeed = memcmp(e.expected().get_block(), data.get_block(),
                                 e.addr().size) == 0;
      if (will_succeed) {
        e = SymEv::CmpXhg(e.data(), e.expected().get_shared_block());
      } else {
        e = SymEv::CmpXhgFail(e.data(), e.expected().get_shared_block());
      }
    }
  }
}

void EventTraceBuilder::recompute_observed(std::vector<Branch> &v) const {
  for (Branch &b : v) {
    clear_observed(b.sym);
  }

  /* When !read_all, last_reads is the set of addresses that have been read
   * (or "are live", if comparing to a liveness analysis).
   * When read_all, last_reads is instead the set of addresses that have *not*
   * been read. All addresses that are not in last_reads are read.
   */
  VecSet<SymAddr> last_reads;
  bool read_all = false;

  for (auto vi = v.end(); vi != v.begin();){
    Branch &vb = *(--vi);
    for (auto ei = vb.sym.end(); ei != vb.sym.begin();){
      SymEv &e = *(--ei);
      switch(e.kind){
      case SymEv::LOAD:
      case SymEv::CMPXHG: /* First a load, then a store */
      case SymEv::CMPXHGFAIL:
        if (read_all)
          last_reads.erase (VecSet<SymAddr>(e.addr().begin(), e.addr().end()));
        else last_reads.insert(VecSet<SymAddr>(e.addr().begin(), e.addr().end()));
        break;
      case SymEv::STORE:
        assert(false); abort();
      case SymEv::UNOBS_STORE:
        if (read_all ^ last_reads.intersects
            (VecSet<SymAddr>(e.addr().begin(), e.addr().end()))){
          e = SymEv::Store(e.data());
        }
        if (read_all)
          last_reads.insert(VecSet<SymAddr>(e.addr().begin(), e.addr().end()));
        else last_reads.erase (VecSet<SymAddr>(e.addr().begin(), e.addr().end()));
        break;
      case SymEv::FULLMEM:
        last_reads.clear();
        read_all = true;
        break;
      default:
        break;
      }
    }
  }
}

void EventTraceBuilder::see_events(const VecSet<int> &seen_accesses){
  for(int i : seen_accesses){
    if(i < 0) continue;
    if (i == prefix_idx) continue;
    IPid fst_pid = prefix[i].iid.get_pid();
    IPid snd_pid = curev().iid.get_pid();
    add_noblock_race(i);
  }
}

void EventTraceBuilder::see_event_pairs
(const VecSet<std::pair<int,int>> &seen_accesses){
  for (std::pair<int,int> p : seen_accesses){
    add_observed_race(p.first, p.second);
  }
}

void EventTraceBuilder::add_noblock_race(int event){
  assert(0 <= event);
  assert(event < prefix_idx);
  assert(do_events_conflict(event, prefix_idx));

  std::vector<Race> &races = curev().races;
  if (races.size()) {
    const Race &prev = races.back();
    if (prev.kind == Race::NONBLOCK
        && prev.first_event == event
        && prev.second_event == prefix_idx) return;
  }
  races.push_back(Race::Nonblock(event,prefix_idx));
}

void EventTraceBuilder::add_lock_suc_race(int lock, int unlock){
  assert(0 <= lock);
  assert(lock < unlock);
  assert(unlock < prefix_idx);

  curev().races.push_back(Race::LockSuc(lock,prefix_idx,unlock));
}

void EventTraceBuilder::add_lock_fail_race(const Mutex &m, int event){
  assert(0 <= event);
  assert(event < prefix_idx);

  lock_fail_races.push_back(Race::LockFail(event,prefix_idx,curev().iid,&m));
}

void EventTraceBuilder::add_observed_race(int first, int second){
  assert(0 <= first);
  assert(first < second);
  assert(second < prefix_idx);
  assert(do_events_conflict(first, second));
  assert(do_events_conflict(second, prefix_idx));

  std::vector<Race> &races = prefix[second].races;
  if (races.size()) {
    const Race &prev = races.back();
    if (prev.kind == Race::OBSERVED
        && prev.first_event == first
        && prev.second_event == second
        && prev.witness_event == prefix_idx)
      return;
  }

  races.push_back(Race::Observed(first,second,prefix_idx));
}

void EventTraceBuilder::add_happens_after(unsigned second, unsigned first){
  assert(first != ~0u);
  assert(second != ~0u);
  assert(first != second);
  assert(first < second);
  assert((long long)second <= prefix_idx);

  std::vector<unsigned> &vec = prefix[second].happens_after;
  if (vec.size() && vec.back() == first) return;

  vec.push_back(first);
}

void EventTraceBuilder::add_happens_after_thread(unsigned second, IPid thread){
  assert((int)second == prefix_idx);
  if (threads[thread].event_indices.empty()) return;
  add_happens_after(second, threads[thread].event_indices.back());
}

void EventTraceBuilder::add_eom(unsigned second, unsigned first){
  assert(first != ~0u);
  assert(second != ~0u);
  assert(first != second);
  assert(first < second);
  assert((long long)second <= prefix_idx);

  std::vector<unsigned> &vec = prefix[second].eom_before;
  if (vec.size() && vec.back() == first) return;

  vec.push_back(first);
}

bool EventTraceBuilder::is_eom_ordered(unsigned second, unsigned first) const{
  assert(first != ~0u);
  assert(second != ~0u);
  assert(first != second);
  if(first >= second) return false;
  assert((long long)second <= prefix.len());
  assert((long long)first <= prefix.len());
  IPid fst = prefix[first].iid.get_pid();
  IPid snd = prefix[second].iid.get_pid();
  int lst_fst = threads[fst].event_indices.back();
  int fst_snd = threads[snd].event_indices.front();
  std::vector<unsigned> eoms = prefix[fst_snd].eom_before;
  return (std::find(eoms.begin(), eoms.end(), lst_fst) != eoms.end());
}

/* Filter the sequence first..last from all elements that are less than
 * any other item. The sequence is modified in place and an iterator to
 * the position beyond the last included element is returned.
 *
 * Assumes less is transitive and asymetric (a strict partial order)
 */
template< class It, class LessFn >
static It frontier_filter(It first, It last, LessFn less){
  It fill = first;
  for (It current = first; current != last; ++current){
    bool include = true;
    for (It check = first; include && check != fill;){
      if (less(*current, *check)){
        include = false;
        break;
      }
      if (less(*check, *current)){
        /* Drop check from fill set */
        --fill;
        std::swap(*check, *fill);
      }else{
        ++check;
      }
    }
    if (include){
      /* Add current to fill set */
      if (fill != current) std::swap(*fill, *current);
      ++fill;
    }
  }
  return fill;
}

//eom is not exactly transitive. We don't need the precise transitive ordering
void EventTraceBuilder::compute_eom(){
  for(IPid i = 2; i<threads.size(); i=i+2){//eom order
    if(threads[i].handler_id == -1) continue;
    for(IPid j = 2; j<threads.size(); j=j+2){
      if(threads[i].handler_id != threads[j].handler_id) continue;
      unsigned fev_i = threads[i].event_indices.front();
      unsigned lev_i = threads[i].event_indices.back();
      unsigned fev_j = threads[j].event_indices.front();
      unsigned lev_j = threads[j].event_indices.back();
      if(fev_j<fev_i) continue;
      if(prefix[fev_i].clock.lt(prefix[lev_j].clock)){
        add_eom(fev_j,lev_i);
      }
    }
  }
}

void EventTraceBuilder::remove_nonreversible_races(){
  for(IPid i = 2; i<threads.size(); i=i+2){
    if(threads[i].handler_id == -1) continue;
    for(IPid j = 2; j<threads.size(); j=j+2){
      if(threads[i].handler_id != threads[j].handler_id) continue;
      if(i == j) continue;
      if(threads[i].event_indices.front() > threads[j].event_indices.front()) continue;
      bool direct_race = false;
      bool indirect_dep = false;
      unsigned last = 0;
      for(unsigned k : threads[j].event_indices){
	if(last == k) continue;
	else last = k;
	std::vector<Race> &races = prefix[k].races;
	for(Race r : races){
	  if(r.first_event > threads[i].event_indices.front() &&
	     prefix[r.first_event].iid.get_pid() != i &&
	     prefix[r.first_event].iid.get_pid() != j &&
	     prefix[threads[i].event_indices.front()].clock.lt
	     (prefix[r.first_event].clock)){
	    indirect_dep = true;
	  }
	}
	for(unsigned ei : prefix[k].happens_after){
	  if(ei > threads[i].event_indices.front() &&
	     prefix[ei].iid.get_pid() != i &&
	     prefix[ei].iid.get_pid() != j &&
	     prefix[threads[i].event_indices.front()].clock.lt
	     (prefix[ei].clock)){
	    indirect_dep = true;
	  }
	}
      }
      last = 0;
      /* keep only the first race between two messeges */
      for(unsigned k : threads[j].event_indices){
	if(last == k) continue;
	else last = k;
	std::vector<Race> &races = prefix[k].races;
	auto end = partition
	  (races.begin(), races.end(),
	   [this, &direct_race, indirect_dep, i](const Race &r){
	     if(prefix[r.first_event].iid.get_pid() == i){
	       if(!indirect_dep && !direct_race){
		 direct_race = true;
		 return true;
	       } else return false;
	     } else{
	       return true;
	     }
	   });
	races.resize(end - races.begin(),races[0]);
      }
    }	  
  }
}

void EventTraceBuilder::clear_vclocks(){
  for(int i=0;i<prefix.len();i++)
    prefix[i].clock = VClock<int>();
  has_vclocks = false;
}

void EventTraceBuilder::compute_vclocks(int pass){
  /* Be idempotent */
  if (has_vclocks) return;

  /* The first event of a thread happens after the spawn event that
   * created it.
   */
  if(pass == 1){
    for (const Thread &t : threads) {
      if (t.spawn_event >= 0 && t.event_indices.size() > 0){
        add_happens_after(t.event_indices[0], t.spawn_event);
      }
      if(t.handler_id != -1 && t.event_indices.size() > 0){
        add_happens_after(t.event_indices[0],
        		  threads[t.handler_id].event_indices.back());
	//TODO: add happensafter to qthread exec event
      }
    }

    /* Move LockFail races into the right event */
    std::vector<Race> final_lock_fail_races;
    for (Race &r : lock_fail_races){
      if (r.second_event < int(prefix.len())) {
        prefix[r.second_event].races.emplace_back(std::move(r));
      } else {
        assert(r.second_event == int(prefix.len()));
        final_lock_fail_races.emplace_back(std::move(r));
      }
    }
    lock_fail_races = std::move(final_lock_fail_races);
  }

  for (unsigned i = 0; i < prefix.len(); i++){
    IPid ipid = prefix[i].iid.get_pid();
    if (prefix[i].iid.get_index() > 1) {
      unsigned last = find_process_event(ipid, prefix[i].iid.get_index()-1);
      prefix[i].clock = prefix[last].clock;
    } else {
      prefix[i].clock = VClock<IPid>();
    }
    prefix[i].clock[ipid] = prefix[i].iid.get_index();

    /* First add the non-reversible edges */
    for (unsigned j : prefix[i].happens_after){
      assert(j < i);
      prefix[i].clock += prefix[j].clock;
    }

    /* Now we want add the possibly reversible edges, but first we must
     * check for reversibility, since this information is lost (more
     * accurately less easy to compute) once we add them to the clock.
     */
    std::vector<Race> &races = prefix[i].races;

    /* First move all races that are not pairs (and thus cannot be
     * subsumed by other events) to the front.
     */
    // TODO: only keep the first race between two messages. Remove other races.
    // Also remove races if messages are not reversible
    auto first_pair = partition(races.begin(), races.end(),
                                [](const Race &r){
                                  return r.kind == Race::NONDET;
                                });

    auto end = races.end();
    bool changed;
    do {
      auto oldend = end;
      changed = false;
      if(pass == 1){
        end = partition
          (first_pair, end,
           [this,i](const Race &r){
	     return !prefix[r.first_event].clock.leq(prefix[i].clock);
           });
      }
      for (auto it = end; it != oldend; ++it){
        if (it->kind == Race::LOCK_SUC){
          prefix[i].clock += prefix[it->unlock_event].clock;
            changed = true;
        }
      }
    } while (changed);
    /* Then filter out subsumed */
    auto fill = end;
    if(pass == 1){
      fill = frontier_filter
	(first_pair, end,
	 [this](const Race &f, const Race &s){
	   /* A virtual event does not contribute to the vclock and cannot
	    * subsume races. */
	   if (s.kind == Race::LOCK_FAIL) return false;
	   /* Also filter out observed races with nonfirst witness */
	   if (f.kind == Race::OBSERVED && s.kind == Race::OBSERVED
	       && f.first_event == s.first_event
	       && f.second_event == s.second_event){
	     /* N.B. We want the _first_ observer as the witness; thus
	      * the reversal of f and s.
	      */
	     return s.witness_event <= f.witness_event;
	   }
	   int se = s.kind == Race::LOCK_SUC ? s.unlock_event : s.first_event;
	   return prefix[f.first_event].clock.leq(prefix[se].clock);
	 });
    }
    /* Add clocks of remaining (reversible) races */
    for (auto it = first_pair; it != fill; ++it){
      if (it->kind == Race::LOCK_SUC){
        assert(prefix[it->first_event].clock.leq
               (prefix[it->unlock_event].clock));
        prefix[i].clock += prefix[it->unlock_event].clock;
      }else if (it->kind != Race::LOCK_FAIL){
        prefix[i].clock += prefix[it->first_event].clock;
      }
    }
    /* Now delete the subsumed races. We delayed doing this to avoid
     * iterator invalidation. */
    races.resize(fill - races.begin(), races[0]);
    if(pass == 2){
      for (unsigned j : prefix[i].eom_before){
        assert(j < i);
        prefix[i].clock += prefix[j].clock;
      }
    }
  }

  has_vclocks = true;
}

bool EventTraceBuilder::record_symbolic(SymEv event){
  if(dryrun) {
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    assert(threads[pid].sleep_sym);
    threads[pid].sleep_sym->push_back(event);
    return true;
  }
  curev().may_conflict = true;
  if (!replay) {
    assert(sym_idx == curev().sym.size());
    /* New event */
    curev().sym.push_back(event);
    sym_idx++;
  } else {
    /* Replay. SymEv::set() asserts that this is the same event as last time. */
    assert(sym_idx < curev().sym.size());
    SymEv &last = curev().sym[sym_idx++];
    if (!last.is_compatible_with(event)) {
      auto pid_str = [this](IPid p) { return threads[p*2].cpid.to_string(); };
      nondeterminism_error("Event with effect " + last.to_string(pid_str)
                           + " became " + event.to_string(pid_str)
                           + " when replayed");
      return false;
    }
    last = event;
  }
  return true;
}

bool EventTraceBuilder::do_events_conflict(int i, int j) const{
  IPid fst = prefix[i].iid.get_pid();
  IPid snd = prefix[j].iid.get_pid();
  if(threads[fst].handler_id != -1 && threads[snd].handler_id != -1 &&
     threads[snd].handler_id == threads[snd].handler_id &&
     (is_eom_ordered(i,j) || is_eom_ordered(j,i))) return true;
     
  return do_events_conflict(prefix[i], prefix[j]);
}

bool EventTraceBuilder::do_events_conflict(const Event &fst,
					   const Event &snd) const{
  return do_events_conflict(fst.iid.get_pid(), fst.sym,
                            snd.iid.get_pid(), snd.sym);
}

static bool symev_has_pid(const SymEv &e) {
  return e.kind == SymEv::SPAWN || e.kind == SymEv::JOIN;
}

static bool symev_is_load(const SymEv &e) {
  return e.kind == SymEv::LOAD || e.kind == SymEv::CMPXHGFAIL;
}

static bool symev_is_unobs_store(const SymEv &e) {
  return e.kind == SymEv::UNOBS_STORE;
}

bool EventTraceBuilder::do_symevs_conflict
(IPid fst_pid, const SymEv &fst,
 IPid snd_pid, const SymEv &snd) const {
  if (fst.kind == SymEv::NONDET || snd.kind == SymEv::NONDET) return false;
  if (fst.kind == SymEv::FULLMEM || snd.kind == SymEv::FULLMEM) return true;
  if (fst.kind == SymEv::POST && snd.kind == SymEv::POST) return false;
  if (symev_is_load(fst) && symev_is_load(snd)) return false;
  if (symev_is_unobs_store(fst) && symev_is_unobs_store(snd)
      && fst.addr() == snd.addr()) return false;

  /* Really crude. Is it enough? */
  if (fst.has_addr()) {
    if (snd.has_addr()) {
      return fst.addr().overlaps(snd.addr());
    } else {
      return false;
    }
  } else {
    return false;
  }
}

bool EventTraceBuilder::do_events_conflict
(IPid fst_pid, const sym_ty &fst,
 IPid snd_pid, const sym_ty &snd) const{
  IPid f_ipid = SPS.get_pid(fst_pid);
  IPid s_ipid = SPS.get_pid(snd_pid);
  if (fst_pid == snd_pid) return true;
  if (threads[f_ipid].handler_id == s_ipid) return true;
  if (threads[f_ipid].handler_id == s_ipid) return true;
  for (const SymEv &fe : fst) {
    if (symev_has_pid(fe) && fe.num() == snd_pid) return true;
    for (const SymEv &se : snd) {
      if (do_symevs_conflict(fst_pid, fe, snd_pid, se)) {
        return true;
      }
    }
  }
  for (const SymEv &se : snd) {
    if (symev_has_pid(se) && se.num() == fst_pid) return true;
  }
  return false;
}

bool EventTraceBuilder::is_observed_conflict
(const Event &fst, const Event &snd, const Event &thd) const{
  return is_observed_conflict(fst.iid.get_pid(), fst.sym,
                              snd.iid.get_pid(), snd.sym,
                              thd.iid.get_pid(), thd.sym);
}

bool EventTraceBuilder::is_observed_conflict
(IPid fst_pid, const sym_ty &fst,
 IPid snd_pid, const sym_ty &snd,
 IPid thd_pid, const sym_ty &thd) const{
  if (fst_pid == snd_pid) return false;
  for (const SymEv &fe : fst) {
    if (fe.kind != SymEv::UNOBS_STORE) continue;
    for (const SymEv &se : snd) {
      if (se.kind != SymEv::STORE
          || !fe.addr().overlaps(se.addr())) continue;
      for (const SymEv &te : thd) {
        if (is_observed_conflict(fst_pid, fe, snd_pid, se, thd_pid, te)) {
          return true;
        }
      }
    }
  }
  return false;
}

bool EventTraceBuilder::is_observed_conflict
(IPid fst_pid, const SymEv &fst,
 IPid snd_pid, const SymEv &snd,
 IPid thd_pid, const SymEv &thd) const {
  assert(fst_pid != snd_pid);
  assert(fst.kind == SymEv::UNOBS_STORE);
  assert(snd.kind == SymEv::STORE);
  assert(fst.addr().overlaps(snd.addr()));
  if (thd.kind == SymEv::FULLMEM) return true;
  return symev_does_load(thd) && thd.addr().overlaps(snd.addr());
}

void EventTraceBuilder::do_race_detect() {
  assert(has_vclocks);
  assert(0 < prefix.size());
  /* Bucket sort races by first_event index */
  std::vector<std::vector<const Race*>> races(prefix.len());
  for (const Race &r : lock_fail_races) races[r.first_event].push_back(&r);
  for (unsigned i = 0; i < prefix.len(); ++i){
    for (const Race &r : prefix[i].races)
      races[r.first_event].push_back(&r);
  }

  /* Do race detection */
  struct obs_sleep sleep;
  for (unsigned i = 0; i < races.size(); ++i){
    obs_sleep_add(sleep, prefix[i]);
    for (const Race *race : races[i]) {
      assert(race->first_event == int(i));
      race_detect_optimal(*race, (const struct obs_sleep&)sleep);
    }
    obs_sleep_wake(sleep, prefix[i]);
  }

  for (unsigned i = 0; i < prefix.len(); ++i) prefix[i].races.clear();
  lock_fail_races.clear();
}

void EventTraceBuilder::race_detect_optimal
(const Race &race, const struct obs_sleep &isleep){
  //llvm::dbgs()<<"Race "<<prefix[race.first_event].iid<<" "<<prefix[race.second_event].iid<<"\n";/////////////

  std::map<IPid, std::vector<unsigned>> eoms;
  std::vector<Branch> v = wakeup_sequence(race, eoms);

  //for(Branch br:v) llvm::dbgs()<<"("<<threads[SPS.get_pid(br.spid)].cpid<<","<<br.index<<")";////////////
  //llvm::dbgs()<<"\n";///////////

  /* Check if we have previously explored everything startable with v */
  if (!sequence_clears_sleep(v, isleep)) return;
  /* Do insertion into the wakeup tree */
  WakeupTreeRef<Branch> node = prefix.parent_at(0);
  while(1) {
    if (!node.size()) {
      /* node is a leaf. That means that an execution that will explore the
       * reversal of this race has already been scheduled.
       */
      return;
    }

    /* skip is used to break out of the loops if we find a child to
     * recurse into (RECURSE), or if the child is incompatible and we
     * need to check the next (NEXT)
     */
    enum { NO, RECURSE, NEXT } skip = NO;
    for (auto child_it = node.begin(); child_it != node.end(); ++child_it) {
      const sym_ty &child_sym = child_it.branch().sym;

      for (auto vei = v.begin(); skip == NO && vei != v.end(); ++vei) {
        const Branch &ve = *vei;
        if (child_it.branch() == ve) {
          if (child_sym != ve.sym) {
            /* This can happen due to observer effects. We must now make sure
             * ve.second->sym does not have any conflicts with any previous
             * event in v; i.e. wether it actually is a weak initial of v.
             */
            for (auto pei = v.begin(); skip == NO && pei != vei; ++pei){
              const Branch &pe = *pei;
              if (do_events_conflict(ve.spid, ve.sym,
                                     pe.spid, pe.sym)){
                skip = NEXT;
              }
            }
            if (skip == NEXT) break;
          }

          if (v.size() == 1) {
            /* v is about to run out, which means that we had already
             * scheduled an execution that was startable with v.
             * From this point, the recursive insertion is a no-op, so
             * exit early.
             */
            return;
          }

          /* We will recurse into this node. To do that we first need to
           * drop all events in child_it.branch() from v.
           */
          if (ve.size < child_it.branch().size) {
            /* child_it.branch() contains more events than just ve.
             * We need to scan v to find all of them.
             */
            int missing = child_it.branch().size - ve.size;
            int spid = ve.spid;
            for (auto vri = v.erase(vei); missing != 0 && vri != v.end();) {
              if (vri->spid == spid) {
                assert(vri->sym.empty());
                if (vri->size > missing) {
                  vri->size = missing;
                  missing = 0;
                  break;
                } else {
                  missing -= vri->size;
                  vri =  v.erase(vri);
                }
              } else {
                ++vri;
              }
            }
          } else if (ve.size > child_it.branch().size) {
            /* ve is larger than child_it.branch(). Delete the common
             * prefix from ve.
             */
            vei->size -= child_it.branch().size;
            vei->sym.clear();
            vei->alt = 0;
          } else {
            /* Drop ve from v. */
            v.erase(vei);
          }
          break;
        }
        else if (do_events_conflict(ve.spid, ve.sym,
				    child_it.branch().spid,
				    child_sym)) {
          /* This branch is incompatible, try the next */
          skip = NEXT;
        }
      }
      if (skip == NEXT) { skip = NO; continue; }

      /* The child is compatible with v, recurse into it. */
      node = child_it.node();
      skip = RECURSE;
      break;

      assert(false && "UNREACHABLE");
      abort();
    }
    if (skip == RECURSE) continue;

    /* No existing child was compatible with v. Insert v as a new sequence. */
    for (Branch &ve : v) {
      if (conf.dpor_algorithm == Configuration::OBSERVERS)
        clear_observed(ve.sym);
      for (SymEv &e : ve.sym) e.purge_data();
      node = node.put_child(std::move(ve));
    }
    branches++;
    return;
  }
}

std::vector<EventTraceBuilder::Branch> EventTraceBuilder::
wakeup_sequence(const Race &race, std::map<IPid, std::vector<unsigned>> &eoms) const{
  int i = race.first_event;
  int j = race.second_event;
  const Event &first = prefix[i];
  IPid fpid = first.iid.get_pid();
  IPid spid = prefix[j].iid.get_pid();
  const bool is_msg_msg_race =
    ((threads[fpid].handler_id != -1) &&
     (threads[fpid].handler_id ==
      threads[spid].handler_id));
  Event second({-1,0});
  Branch second_br(0,0);
  recompute_second(race,second_br,second);

  /* v is the subsequence of events in prefix come after prefix[i],
   * but do not "happen after" (i.e. their vector clocks are not strictly
   * greater than prefix[i].clock), followed by the second event.
   *
   * It is the sequence we want to insert into the wakeup tree.
   */
  std::vector<Branch> v;
  std::vector<const Event*> observers;
  std::vector<Branch> notobs;
  bool in_v[prefix.len()];
  unsigned fst_of_fst = threads[fpid].event_indices.front();
  unsigned br_point;
  if(is_msg_msg_race) br_point = fst_of_fst;
  else br_point = i;

  /* notdep and notobs computation */
  {
    /* partial_msg[k] = true iff k is partial in v */ 
    bool partial_msg[threads.size()];
    /* last partial message is considered for a handler */
    bool a[threads.size()];
    /* w is sequence of partial messages and events */
    bool in_w[prefix.len()];

    for(int k = 0; k < int(threads.size()); ++k){
      partial_msg[k] = false;
      a[k] = false;
    }

    /* from start to br_point the wakeup sequence
     * is same as the current execution
     */
    for (unsigned k = 0; k < br_point; ++k){
      v.emplace_back(branch_with_symbolic_data(k));
      in_v[k] = true;
    }

    /* in_v[k] is true if prefix[k] does not "happen after" prefix[i]
     * (their vector clocks are not strictly greater than prefix[i].clock).
     */
    for (unsigned k = br_point; k < int(prefix.len()); ++k){
      if(!prefix[br_point].clock.leq(prefix[k].clock)){
	in_v[k] = true;
      } else if (race.kind == Race::OBSERVED && k != j) {
	if (!std::any_of(observers.begin(), observers.end(),
			 [this,k](const Event* o){
			   return o->clock.leq(prefix[k].clock); })){
	  if (is_observed_conflict(first, second, prefix[k])){
	    assert(!observers.empty() || k == race.witness_event);
	    observers.push_back(&prefix[k]);
	  } else if (race.kind == Race::OBSERVED) {
	    notobs.emplace_back(branch_with_symbolic_data(k));
	  }
	}
      } else {
	in_v[k] = false;
	IPid ipid = prefix[k].iid.get_pid();
	if(threads[ipid].handler_id != -1){
	  partial_msg[ipid] = true;
	}
      }
      in_w[k]=false;
    }

    /* remove partial messages and the events from in_v 
     * that are happens after some partial message
     * in_w contains events of first partial message of */
    for(unsigned k = br_point; k < int(prefix.len()); ++k){
      IPid ipid = prefix[k].iid.get_pid();
      in_w[k] = true;
      if(in_v[k] == false){
	if(threads[ipid].handler_id != -1) a[threads[ipid].handler_id] = true;
	in_w[k] = false;
	continue;
      }
      // v[k] is true
      if(partial_msg[ipid] == true && ipid != spid){
	if(a[threads[ipid].handler_id] == true){
	  in_w[k] = false;
	}
	in_v[k] = false;
	continue;
      }
      // // not a partial msg
      // if(threads[ipid].handler_id != -1 &&
      //    a[threads[ipid].handler_id] == true){
      //   in_w[k] = false;
      //   continue;
      // }
      // //no partial msg before in the handler
      // for (unsigned h : prefix(k).happens_after){
      //   if(in_v[h] == false){
      //     if(in_w[h] == false) in_w[k] = false;
      //     in_v[k] = false;
      //     break;
      //   }
      // }
      // if(in_v[k] == false && in_w[k] == false) continue;
      // for (auto race : prefix(k).races){
      //   unsigned h = race.first_event; 
      //   if(in_v[h] == false){
      // 	if(in_w[h] == false) in_w[k] = false;
      //     in_v[k] = false;
      //     break;
      //   }
      // }
      // if(in_v[k] == false && in_w[k] == false) continue;
      // for (unsigned h : prefix(k).eom_before){
      //   if(in_v[h] == false){
      //     if(in_w[h] == false) in_w[k] = false;
      //     in_v[k] = false;
      //     break;
      //   }
      // }
    }

    /* inserting notdep in v */
    for (unsigned k = br_point; k < prefix.len(); ++k){
      if(in_v[k] == true) v.emplace_back(branch_with_symbolic_data(k));
    }
  }
  if(is_msg_msg_race){
    //TODO: Include in_w
    /* Include part of second message */
    for(unsigned k = threads[spid].event_indices.front();
	k < j; k++){
      if(in_v[k] == false &&
	 prefix[k].iid.get_pid() != fpid &&
         prefix[k].clock.lt(prefix[j].clock)){
        v.emplace_back(branch_with_symbolic_data(k));
	in_v[k] = true;
      }
    }
  }

  if (race.kind == Race::NONBLOCK) {
    recompute_cmpxhg_success(second_br.sym, v, br_point);
  }
  v.push_back(std::move(second_br));
  //TODO: Works only for NONBLOCK race. Find actual j and make in_v[j] true
  in_v[j] = true;

  /* Part of the first message of the race */
  if(is_msg_msg_race){
    std::vector<Branch> fst_msg;
    for (unsigned k = br_point; k < i; ++k){
      if(prefix[k].clock.lt(prefix[i].clock)){
	fst_msg.emplace_back(branch_with_symbolic_data(k));
      }
    }
  }

  if (race.kind == Race::OBSERVED) {
    int k = race.witness_event;
    Branch first_br = branch_with_symbolic_data(i);
    Branch witness_br = branch_with_symbolic_data(k);
    /* Only replay the racy event. */
    witness_br.size = 1;
    
    v.emplace_back(std::move(first_br));
    v.back().spid = threads[prefix[i].iid.get_pid()].spid;
    v.insert(v.end(), std::make_move_iterator(notobs.begin()),
             std::make_move_iterator(notobs.end()));
    notobs.clear(); /* Since their states are undefined after std::move */
    v.emplace_back(std::move(witness_br));
    v.back().spid = threads[prefix[k].iid.get_pid()].spid;
  }

  /* collect eoms within WS*/
  for(IPid k = 2; k < threads.size(); k=k+2){
    if(threads[k].handler_id == -1) continue;
    unsigned last_ev = threads[k].event_indices.back();
    if(in_v[last_ev] == true){
      eoms[k] = prefix[threads[k].event_indices.front()].eom_before;
    }
  }

  if (conf.dpor_algorithm == Configuration::OBSERVERS) {
    /* Recompute observed states on events in v */
    recompute_observed(v);
  }
  return v;
}

void EventTraceBuilder::
recompute_second(const Race &race, Branch &second_br, Event &second) const{
  int i = race.first_event;
  int j = race.second_event;
  const Event &first = prefix[i];
  if (race.kind == Race::LOCK_FAIL) {
    second = reconstruct_lock_event(race);
    /* XXX: Lock events don't have alternatives, right? */
    second_br = Branch(threads[second.iid.get_pid()].spid,second.iid.get_index());
    second_br.sym = std::move(second.sym);
  } else if (race.kind == Race::NONDET) {
    second = first;
    second_br = branch_with_symbolic_data(i);
    second_br.alt = race.alternative;
  } else {
    second = prefix[j];
    second.sleep.clear();
    second.wakeup.clear();
    second_br = branch_with_symbolic_data(j);
  }
  if (race.kind != Race::OBSERVED) {
    /* Only replay the racy event. */
    second_br.size = 1;
  }
}

std::vector<int> EventTraceBuilder::iid_map_at(int event) const{
  std::vector<int> map(threads.size(), 1);
  for (int i = 0; i < event; ++i) {
    iid_map_step(map, prefix.branch(i));
  }
  return map;
}

void EventTraceBuilder::iid_map_step(std::vector<int> &iid_map, const Branch &event) const{
  if (iid_map.size() <= unsigned(event.spid)) iid_map.resize(event.spid+1, 1);
  iid_map[event.spid] += event.size;
}

void EventTraceBuilder::iid_map_step_rev(std::vector<int> &iid_map, const Branch &event) const{
  iid_map[event.spid] -= event.size;
}

EventTraceBuilder::Event EventTraceBuilder::
reconstruct_lock_event(const Race &race) const {
  assert(race.kind == Race::LOCK_FAIL);
  Event ret(race.second_process);
  /* Compute the clock of the locking process (event k in prefix is
   * something unrelated since this is a lock probe) */
  /* Find last event of p before this mutex probe */
  IPid p = race.second_process.get_pid();
  if (race.second_process.get_index() != 1) {
    int last = find_process_event(p, race.second_process.get_index()-1);
    ret.clock = prefix[last].clock;
  }
  /* Recompute the clock of this mutex_lock_fail */
  ++ret.clock[p];

  assert(std::any_of(prefix[race.first_event].sym.begin(),
                     prefix[race.first_event].sym.end(),
                     [](const SymEv &e){ return e.kind == SymEv::M_LOCK
                         || e.kind == SymEv::FULLMEM; }));
  ret.sym = prefix[race.first_event].sym;
  return ret;
}

inline std::pair<bool,unsigned> EventTraceBuilder::
try_find_process_event(IPid pid, int index) const{
  assert(pid >= 0 && pid < int(threads.size()));
  assert(index >= 1);
  if (index > int(threads[pid].event_indices.size())){
    return {false, ~0};
  }

  unsigned k = threads[pid].event_indices[index-1];
  assert(k < prefix.len());
  assert(prefix.branch(k).size > 0);
  assert(prefix[k].iid.get_pid() == pid
         && prefix[k].iid.get_index() <= index
         && (prefix[k].iid.get_index() + prefix.branch(k).size) > index);

  return {true, k};
}

inline unsigned EventTraceBuilder::find_process_event(IPid pid, int index) const{
  assert(pid >= 0 && pid < int(threads.size()));
  assert(index >= 1 && index <= int(threads[pid].event_indices.size()));
  unsigned k = threads[pid].event_indices[index-1];
  assert(k < prefix.len());
  assert(prefix.branch(k).size > 0);
  assert(prefix[k].iid.get_pid() == pid
         && prefix[k].iid.get_index() <= index
         && (prefix[k].iid.get_index() + prefix.branch(k).size) > index);

  return k;
}

bool EventTraceBuilder::has_pending_store(IPid pid, SymAddr ml) const {
  const std::vector<PendingStore> &sb = threads[pid].store_buffer;
  for(unsigned i = 0; i < sb.size(); ++i){
    if(sb[i].ml.includes(ml)){
      return true;
    }
  }
  return false;
}

#ifndef NDEBUG
#  define IFDEBUG(X) X
#else
#  define IFDEBUG(X) ((void)0)
#endif

void EventTraceBuilder::wakeup(Access::Type type, SymAddr ml){
  IPid pid = curev().iid.get_pid();
  IFDEBUG(sym_ty ev);
  std::vector<IPid> wakeup; // Wakeup these
  switch(type){
  case Access::W_ALL_MEMORY:
    {
      IFDEBUG(ev.push_back(SymEv::Fullmem()));
      for(unsigned p = 0; p < threads.size(); ++p){
        if(threads[p].sleep_full_memory_conflict ||
           threads[p].sleep_accesses_w.size()){
          wakeup.push_back(p);
        }else{
          for(SymAddr b : threads[p].sleep_accesses_r){
            if(!has_pending_store(p,b)){
              wakeup.push_back(p);
              break;
            }
          }
        }
      }
      break;
    }
  case Access::R:
    {
      IFDEBUG(ev.push_back(SymEv::Load(SymAddrSize(ml,1))));
      for(unsigned p = 0; p < threads.size(); ++p){
        if(threads[p].sleep_full_memory_conflict ||
           (int(p) != pid+1 &&
            threads[p].sleep_accesses_w.count(ml))){
          wakeup.push_back(p);
        }
      }
      break;
    }
  case Access::W:
    {
      /* We don't pick the right value, but it should not matter */
      IFDEBUG(ev.push_back(SymEv::Store({SymAddrSize(ml,1), 1})));
      for(unsigned p = 0; p < threads.size(); ++p){
        if(threads[p].sleep_full_memory_conflict ||
           (int(p) + 1 != pid &&
            (threads[p].sleep_accesses_w.count(ml) ||
             (threads[p].sleep_accesses_r.count(ml) &&
              !has_pending_store(p,ml))))){
          wakeup.push_back(p);
        }
      }
      break;
    }
  default:
    throw std::logic_error("EventTraceBuilder::wakeup: Unknown type of memory access.");
  }

#ifndef NDEBUG
  if (conf.dpor_algorithm != Configuration::SOURCE) {
    VecSet<IPid> wakeup_set(wakeup);
    for (unsigned p = 0; p < threads.size(); ++p){
      if (!threads[p].sleeping) continue;
      assert(threads[p].sleep_sym);
      assert(bool(wakeup_set.count(p))
             == do_events_conflict(pid, ev, p, *threads[p].sleep_sym));
    }
  }
#endif

  for(IPid p : wakeup){
    assert(threads[p].sleeping);
    threads[p].sleep_accesses_r.clear();
    threads[p].sleep_accesses_w.clear();
    threads[p].sleep_full_memory_conflict = false;
    threads[p].sleep_sym = nullptr;
    threads[p].sleeping = false;
    curev().wakeup.insert(p);
  }
}

bool EventTraceBuilder::has_cycle(IID<IPid> *loc) const{
  int proc_count = threads.size();
  int pfx_size = prefix.len();

  /* Identify all store events */
  struct stupd_t{
    /* The index part of the IID identifying a store event. */
    int store;
    /* The index in prefix of the corresponding update event. */
    int update;
  };
  /* stores[proc] is all store events of process proc, ordered by
   * store index.
   */
  std::vector<std::vector<stupd_t> > stores(proc_count);
  for(int i = 0; i < pfx_size; ++i){
    if(prefix[i].iid.get_pid() % 2){ // Update
      assert(prefix[i].origin_iid.get_pid()
             == prefix[i].iid.get_pid()-1);
      stores[prefix[i].iid.get_pid() / 2].push_back
        ({prefix[i].origin_iid.get_index(),i});
    }
  }

  /* Attempt to replay computation under SC */
  struct proc_t {
    proc_t()
      : pc(0), pfx_index(0), store_index(0), blocked(false), block_clock() {};
    int pc; // Current program counter
    int pfx_index; // Index into prefix
    int store_index; // Index into stores
    bool blocked; // Is the process currently blocked?
    VClock<IPid> block_clock; // If blocked, what are we waiting for?
  };
  std::vector<proc_t> procs(proc_count);

  int proc = 0; // The next scheduled process
  /* alive keeps track of whether any process has been successfully
   * scheduled lately
   */
  bool alive = false;
  while(true){
    // Advance pfx_index to the right Event in prefix
    while(procs[proc].pfx_index < pfx_size &&
          prefix[procs[proc].pfx_index].iid.get_pid() != proc*2){
      ++procs[proc].pfx_index;
    }
    if(pfx_size <= procs[proc].pfx_index){
      // This process is finished
      proc = (proc+1)%proc_count;
      if(proc == 0){
        if(!alive) break;
        alive = false;
      }
      continue;
    }

    int next_pc = procs[proc].pc+1;
    const Event &evt = prefix[procs[proc].pfx_index];
    const Branch &branch = prefix.branch(procs[proc].pfx_index);

    if(!procs[proc].blocked){
      assert(evt.iid.get_pid() == 2*proc);
      assert(evt.iid.get_index() <= next_pc);
      assert(next_pc < evt.iid.get_index() + branch.size);
      procs[proc].block_clock = evt.clock;
      assert(procs[proc].block_clock[proc*2] <= next_pc);
      procs[proc].block_clock[proc*2] = next_pc;
      if(procs[proc].store_index < int(stores[proc].size()) &&
         stores[proc][procs[proc].store_index].store == next_pc){
        // This is a store. Also consider the update's clock.
        procs[proc].block_clock
          += prefix[stores[proc][procs[proc].store_index].update].clock;
        ++procs[proc].store_index;
      }
    }

    // Is this process blocked?
    // Is there some process we have to wait for?
    {
      int i;
      procs[proc].blocked = false;
      for(i = 0; i < proc_count; ++i){
        if(i != proc && procs[i].pc < procs[proc].block_clock[i*2]){
          procs[proc].blocked = true;
          break;
        }
      }
    }

    // Are we still blocked?
    if(procs[proc].blocked){
      proc = (proc+1)%proc_count; // Try another process
      if(proc == 0){
        if(!alive) break;
        alive = false;
      }
    }else{
      alive = true;
      procs[proc].pc = next_pc;
      assert(next_pc == procs[proc].block_clock[proc*2]);

      // Advance pc to next interesting event
      next_pc = evt.iid.get_index() + branch.size - 1;
      if(procs[proc].store_index < int(stores[proc].size()) &&
         stores[proc][procs[proc].store_index].store-1 < next_pc){
        next_pc = stores[proc][procs[proc].store_index].store-1;
      }
      assert(procs[proc].pc <= next_pc);
      procs[proc].pc = next_pc;

      if(next_pc + 1 == evt.iid.get_index() + branch.size){
        // We are done with this Event
        ++procs[proc].pfx_index;
      }
    }
  }

  // Did all processes finish, or are some still blocked?
  {
    int upd_idx = -1; // Index of the latest update involved in a cycle
    bool has_cycle = false;
    for(int i = 0; i < proc_count; ++i){
      if(procs[i].blocked){
        // There is a cycle
        has_cycle = true;
        int next_pc = procs[i].pc+1;
        if(0 < procs[i].store_index && stores[i][procs[i].store_index-1].store == next_pc){
          if(stores[i][procs[i].store_index-1].update > upd_idx){
            upd_idx = stores[i][procs[i].store_index-1].update;
            *loc = prefix[upd_idx].iid;
          }
        }
      }
    }
    assert(!has_cycle || 0 <= upd_idx);
    return has_cycle;
  }
}

long double EventTraceBuilder::estimate_trace_count() const{
  return estimate_trace_count(0);
}

long double EventTraceBuilder::estimate_trace_count(int idx) const{
  if(idx > int(prefix.len())) return 0;
  if(idx == int(prefix.len())) return 1;

  long double count = 1;
  for(int i = int(prefix.len())-1; idx <= i; --i){
    count += prefix[i].sleep_branch_trace_count;
    count += std::max(0, int(prefix.children_after(i)))
      * (count / (1 + prefix[i].sleep.size()));
  }

  return count;
}

