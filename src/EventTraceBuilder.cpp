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
#include <forward_list>

#define ANSIRed "\x1b[91m"
#define ANSIRst "\x1b[m"

static void clear_observed(sym_ty &syms);
static std::string events_to_string(const llvm::SmallVectorImpl<SymEv> &e);

EventTraceBuilder::
EventTraceBuilder(const Configuration &conf) : TSOPSOTraceBuilder(conf) {
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
    }else if(prefix_idx + 1 == int(prefix.len()) &&
	     prefix.lastnode().size() == 0){

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
      IPid pid = SPS.get_pid(prefix[prefix_idx+1].sleep[dry_sleepers]);
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
    assert(int(threads[curev().iid.get_pid()].event_indices.back()) ==
	   prefix_idx + 1);
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
       (conf.max_search_depth < 0 ||
	threads[p].last_event_index() < conf.max_search_depth)){
      threads[p].event_indices.push_back(++prefix_idx);
      assert(prefix_idx == int(prefix.len()));
      prefix.push(Branch(threads[p].spid,threads[p].last_event_index()),
		  Event(IID<IPid>(IPid(p),threads[p].last_event_index())));
      *proc = p/2;
      *aux = 0;
      return true;
    }
  }

  for(p = 0; p < sz; p += 2){ // Loop through real threads
    if(threads[p].available && !threads[p].sleeping &&
       (conf.max_search_depth < 0 ||
	threads[p].last_event_index() < conf.max_search_depth)){
      threads[p].event_indices.push_back(++prefix_idx);
      assert(prefix_idx == int(prefix.len()));
      prefix.push(Branch(threads[p].spid,threads[p].last_event_index()),
		  Event(IID<IPid>(IPid(p),threads[p].last_event_index())));
      *proc = p/2;
      *aux = -1;
      return true;
    }
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
  return ((prefix.len() <= 0) ||
	  (prefix_idx + 1 < int(prefix.len())) ||
	  (prefix.lastnode().size() != 0));
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
  if(!dryrun){
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
  compute_vclocks();

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
  compute_vclocks();
  // llvm::dbgs() << " Trace:=====> \n";
  //   for(auto p : currtrace){
  //     llvm::dbgs()<<"(("<<threads[p.first.get_pid()].cpid<<","<<p.first.get_index()<<"),("
  // 		  <<threads[p.second.get_pid()].cpid<<","<<p.second.get_index()<<"))\n";
  //   }
  /* Checking if current exploration is redundant */
  // auto trace_it = Traces.find(currtrace);
  // if(trace_it != Traces.end()){
  //   llvm::dbgs() << "|| ERROR: Redundant exploration ================\n";
  //   debug_print();
  //   llvm::dbgs() << " =============================\n";
  //   llvm::dbgs() << " Trace:=====> \n";
  //   for(auto p : (*trace_it)){
  //     llvm::dbgs()<<"(("<<threads[p.first.get_pid()].cpid<<","<<p.first.get_index()<<"),("
  // 		  <<threads[p.second.get_pid()].cpid<<","<<p.second.get_index()<<"))\n";
  //   }
  //   return false;
  // }
  // Traces.insert(std::move(currtrace));

  do_race_detect();

  if(conf.debug_print_on_reset){
    llvm::dbgs() << " === EventTraceBuilder reset ===\n";
    debug_print();
    llvm::dbgs() << " =============================\n";
  }

  if(max_branches < branches) max_branches = branches;
  if(max_pending_WSs < no_of_pending_WSs) max_pending_WSs = no_of_pending_WSs;
  branches--;
#ifndef NDEBUG
  /* The if-statement is just so we can control which test cases need to
   *  satisfy this assertion for now. Eventually, all should.
   */
  if(conf.dpor_algorithm != Configuration::SOURCE){
    //check_symev_vclock_equiv();
  }
#endif

  unsigned i;
  for(i = unsigned(prefix.len())-1; 0 <= i; --i){
    if(prefix.children_after(i)){
      break;
    }
    else if(i == 0){
      /* No more branching is possible. */
      return false;
    }
  }

  replay_point = i;

  /* Store explored branches of different messages */
  for(unsigned k = prefix.len()-1; k >= i ; k--){
    IPid ipid = prefix[k].iid.get_pid();
    done_trees_t &explored_tails = prefix[k].explored_tails;
    if(k < prefix.len()-1) explored_tails = std::move(prefix[k+1].explored_tails);
    /* add prefix[k] into sleep tree of same message */
    if(threads[ipid].handler_id != -1 &&
       threads[ipid].event_indices.front() <= i){
      // TODO: Else if prefix[k] is conflicting with last event of
      // some message in explored_tails, then do same
      if(k == prefix.len()-1 ||
	 explored_tails[threads[ipid].spid].empty()){
	if(prefix.branch(k).access_global()){
	  //TODO: collect all global events(locks,conds,mutexes,...)
  	  explored_tails[threads[ipid].spid].emplace(1,prefix.branch(k));
	}
	continue;
      }
      for(auto slp_tree_it = explored_tails.begin();
	  slp_tree_it != explored_tails.end(); slp_tree_it++){
        if(slp_tree_it->first == threads[ipid].spid &&
	   prefix.branch(k).access_global()){
	  std::set<std::list<Branch>> tail_set;
	  for(auto tail : slp_tree_it->second){
	    std::list<Branch> new_tail = std::move(tail);
	    new_tail.push_front(prefix.branch(k));
	    tail_set.insert(new_tail);
	  }
	  slp_tree_it->second = std::move(tail_set);
	}
      }
    }
  }
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
    // evt.done_msgs = prev_evt.done_msgs;
    if(br.spid != threads[prev_evt.iid.get_pid()].spid){
      // if(threads[prev_evt.iid.get_pid()].handler_id != -1 &&
      //    prefix[i-1].iid.get_pid() != prev_evt.iid.get_pid()){
      // 	evt.done_msgs.push_back(threads[prev_evt.iid.get_pid()].spid);
      // }
      // else{
      if(threads[prev_evt.iid.get_pid()].handler_id == -1 ||
	 prev_evt.iid.get_index() > 1){
        evt.sleep.insert(threads[prev_evt.iid.get_pid()].spid);
      }
    }
    evt.sleep_branch_trace_count = sleep_branch_trace_count;
    /* Copying explored_tails and sleep_trees to the new event */
    if(!prev_evt.sleep_trees.empty())
      evt.sleep_trees = std::move(prev_evt.sleep_trees);
    if(prev_evt.iid.get_index() == 1 &&
       threads[prev_evt.iid.get_pid()].handler_id != -1){
      IPid ispid = threads[prev_evt.iid.get_pid()].spid;
      evt.sleep_trees[ispid] =
    	std::move(prev_evt.explored_tails[ispid]);
      prev_evt.explored_tails.erase(ispid);
    }
    if(!prev_evt.explored_tails.empty())
      evt.explored_tails = std::move(prev_evt.explored_tails);

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
  blocked_awaits.clear();
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
IID<CPid> EventTraceBuilder::get_iid(unsigned i) const{
  IPid pid = prefix[i].iid.get_pid();
  int idx = prefix[i].iid.get_index();
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

std::string EventTraceBuilder::iid_string(const Branch &branch, unsigned index) const{
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
bool EventTraceBuilder::wut_string_add_node
(std::vector<std::string> &lines, std::vector<int> &iid_map,
 unsigned line, Branch branch, WakeupTreeRef<Branch> node) const{
  unsigned offset = 2 + ((lines.size() < line)?0:lines[line].size());

  std::vector<std::pair<Branch,WakeupTreeRef<Branch>>> nodes({{branch,node}});
  iid_map_step(iid_map, branch);
  unsigned l = line;
  WakeupTreeRef<Branch> n = node;
  Branch b = branch;
  bool res = true;
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
      
      res &= wut_string_add_node(lines, iid_map, l+1, ci.branch(), ci.node());
    }
    iid_map_step_rev(iid_map, b);
    while(lines[l].size() < offset) lines[l] += " ";
    // assert(b.index == iid_map[b.spid]);
    lines[l] += " " + iid_string(b, iid_map[b.spid]);
    if(b.index != iid_map[b.spid]){
      lines[l]+= std::to_string(b.index) + "----w";////////////////
      res &= false;
    }

    nodes.pop_back();
  }
  return res;
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
          clock_offs = std::max(clock_offs,
				int(prefix[k].clock.to_string().size()));
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
  sleep_trees_t sleep_trees;
  std::vector<bool> handler_busy(threads.size(), false);
  std::vector<std::vector<bool>>
    busy_n_hap_aft_witness(SPS.num_of_threads(),
			   std::vector<bool>(threads.size(), false));
  bool multiple_handlers;
  IPid last_handler = -1;

  for(unsigned i = 0; i < prefix.len(); ++i){
    IPid ipid = prefix[i].iid.get_pid();
    unsigned index = prefix[i].iid.get_index();
    IPid handler = threads[ipid].handler_id;
    if(!multiple_handlers && handler != -1){
      if(last_handler != -1 && handler != last_handler)
	multiple_handlers = true;
      last_handler = handler;
    }
    iid_offs = std::max(iid_offs,2*ipid+int(iid_string(i).size()));
    symev_offs = std::max(symev_offs,
                          int(events_to_string(prefix[i].sym).size()));
    obs_sleep_add(sleep_set, sleep_trees, prefix[i], handler_busy);
    lines.push_back(" SLP:" + oslp_string(sleep_set));

    /* Add events in the witness events */
    update_witness_sets(index, prefix[i].end_of_msg(), handler,
			prefix[i].clock, sleep_trees, busy_n_hap_aft_witness);
    if(handler != -1){
      if(index == 1) handler_busy[handler]=true;
      else if(prefix[i].end_of_msg()) handler_busy[handler]=false;
    }
    obs_sleep_wake(sleep_set, sleep_trees, threads[ipid].spid,
		   prefix[i].iid.get_index(),
		   prefix[i].clock, prefix[i].sym, multiple_handlers);
  }

  for(const auto &ab : blocked_awaits) {
    for (const auto &pa : ab.second) {
      IPid ipid = pa.first;
      const auto &a = pa.second;
      iid_offs = std::max(iid_offs,2*ipid+int(iid_string(Branch(ipid, 0),a.index).size()));
      symev_offs = std::max(symev_offs,
                            int(a.ev.to_string().size()));
      lines.push_back("");
    }
  }

  /* Add wakeup tree */
  bool res = true;
  std::vector<int> iid_map = iid_map_at(prefix.len());
  for(int i = prefix.len()-1; 0 <= i; --i){
    auto node = prefix.parent_at(i);
    iid_map_step_rev(iid_map, prefix.branch(i));
    for (auto it = node.begin(); it != node.end(); ++it) {
      Branch b = it.branch();
      if (b == prefix.branch(i)) continue; /* Only print others */
      res &= wut_string_add_node(lines, iid_map, i, it.branch(), it.node());
    }
  }
  // /* print sleep tree */
  // for(unsigned i = 0; i < prefix.len(); ++i){
  //   lines[i] += " [";
  //   sleep_trees_t explored_tails = prefix[i].sleep_trees;
  //   for(auto it = explored_tails.begin(); it != explored_tails.end(); it++){
  //     lines[i] += std::to_string(it->first) + " -> {";
  //     const std::vector<std::list<Branch>> tails = it->second;
  //     for(auto seq_it = tails.begin(); seq_it != tails.end(); seq_it++){
  // 	lines[i] += "<";
  // 	std::list<Branch> seq = *seq_it;
  // 	for(auto br : seq){
  // 	  lines[i] += events_to_string(br.sym) + ",";
  // 	}
  // 	lines[i] += ">";
  //     }
  //     lines[i] += "}, "; 
  //   }
  //   lines[i] += "]";
  // }

  unsigned i = 0;
  for(; i < prefix.len(); ++i){
    IPid ipid = prefix[i].iid.get_pid();
    llvm::dbgs() << rpad("",2+ipid*2)
                 << rpad(iid_string(i),iid_offs-ipid*2)
                 << " " << rpad(events_to_string(prefix[i].sym),symev_offs)
      // << " " << prefix[i].clock/////////////
                 << lines[i] << "\n";
  }
  for(const auto &ab : blocked_awaits) {
    for (const auto &pb : ab.second) {
      IPid ipid = pb.first;
      const auto &b = pb.second;
      llvm::dbgs() << " b"
                   << rpad("",ipid*2)
                   << rpad(iid_string(Branch(ipid, 0),b.index),iid_offs-ipid*2)
                   << " " << rpad(b.ev.to_string(),symev_offs)
                   << lines[i++] << "\n";
    }
  }
  for (; i < lines.size(); ++i){
    llvm::dbgs() << std::string(2+iid_offs + 1+symev_offs, ' ')
		 << lines[i] << "\n";
  }
  if(errors.size()){
    llvm::dbgs() << "Errors:\n";
    for(unsigned i = 0; i < errors.size(); ++i){
      llvm::dbgs() << "  Error #" << i+1 << ": "
                   << errors[i]->to_string() << "\n";
    }
  }
  assert(res);
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
bool EventTraceBuilder::create(){
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
  return true;
}

bool EventTraceBuilder::returnev(){
  return record_symbolic(SymEv::Ret());
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
  bool res = create();
  threads[threads.size()-2].handler_id = tpid;
  threads[threads.size()-1].handler_id = tpid;
  return (res && record_symbolic(SymEv::Post(threads[threads.size()-2].spid)));
}

bool EventTraceBuilder::store(const SymData &sd){
  if(dryrun) return true;
  curev().may_conflict = true; /* prefix_idx might become bad otherwise */
  IPid ipid = curev().iid.get_pid();
  threads[ipid].store_buffer.push_back(PendingStore(sd.get_ref(),
						    prefix_idx,last_md));
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
    || e.kind == SymEv::CMPXHG|| e.kind == SymEv::RMW
    || e.kind == SymEv::XCHG_AWAIT;
}

static VecSet<int> to_vecset_and_clear
(boost::container::flat_map<int,unsigned> &set) {
  VecSet<int> ret;
  for (const auto &el : std::move(set)) {
    ret.insert(el.second);
  }
  set.clear();
  return ret;
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
    IPid pid = SPS.get_pid(prefix[prefix_idx+1].sleep[dry_sleepers-1]);
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
  VecSet<std::pair<int,int>> seen_pairs;

  /* See previous updates reads to ml */
  for(SymAddr b : ml){
    ByteInfo &bi = mem[b];
    int lu = bi.last_update;
    assert(lu < int(prefix.len()));
    bool lu_before_read = false;
    for(int i : bi.last_read){
      if (i < 0) continue;
      const IPid last_read_pid = prefix[i].iid.get_pid();
      if(last_read_pid != tipid) seen_accesses.insert(i);
      if (lu >= 0 && i > lu && prefix[lu].iid.get_pid() != last_read_pid+1)
        lu_before_read = true;
    }

    if (lu_before_read) {
      bi.unordered_updates.clear();
      bi.before_unordered.clear(); // No need to add loads (?)
    } else if(0 <= lu) {
      sym_ty &lu_sym = prefix[lu].sym;
      if (lu_sym.size() != 1
          || lu_sym[0].kind != SymEv::UNOBS_STORE
          || lu_sym[0].addr() != ml) {
        observe_memory(b, bi, seen_accesses, seen_pairs, true);
      } else {
        seen_accesses.insert(bi.before_unordered);
      }
    }

    /* Register in memory */
    if (conf.dpor_algorithm == Configuration::OBSERVERS) {
      // bi.unordered_updates.insert_geq(prefix_idx);
      bi.unordered_updates[ipid] = prefix_idx;
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
  see_event_pairs(seen_pairs);
}

/* This predicate has to be transitive. */
static bool rmwaction_commutes(const Configuration &conf,
                               RmwAction::Kind lhs, bool lhs_used,
                               RmwAction::Kind rhs, bool rhs_used) {
  // if (!conf.commute_rmws) return false;
  // if (lhs_used || rhs_used) return false;
  // using Kind = RmwAction::Kind;
  // switch(lhs) {
  // case Kind::ADD: case Kind::SUB:
  //   return (rhs == Kind::ADD || rhs == Kind::SUB);
  // case Kind::XCHG:
  //   return false;
  // default:
  //   /* All kinds except for XCHG commutes with themselves */
  //   return rhs == lhs;
  // }
  return false;
}

bool EventTraceBuilder::atomic_rmw(const SymData &sd, RmwAction action) {
  if (!record_symbolic(SymEv::Rmw(sd, action))) return false;
  const SymAddrSize &ml = sd.get_ref();
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    VecSet<SymAddr> &R = threads[pid].sleep_accesses_r;
    VecSet<SymAddr> &W = threads[pid].sleep_accesses_w;
    for(SymAddr b : ml){
      R.insert(b);
      W.insert(b);
    }
    return true;
  }
  IPid ipid = curev().iid.get_pid();
  assert(ipid % 2 == 0);

  { // Add the clock of the auxiliary thread (because of fence semantics)
    assert(threads[ipid].store_buffer.empty());
    add_happens_after_thread(prefix_idx, ipid+1);
  }

  VecSet<int> seen_accesses;
  VecSet<std::pair<int,int>> seen_pairs;

  /* See previous updates & reads to ml */
  for(SymAddr b : ml){
    ByteInfo &bi = mem[b];
    int lu = bi.last_update;
    const SymAddrSize &lu_ml = bi.last_update_ml;
    bool conflicts_with_lu = false, lu_before_read = false;
    assert(lu < int(prefix.len()));

    for(int i : bi.last_read){
      if (i < 0) continue;
      const IPid last_read_pid = prefix[i].iid.get_pid();
      if(last_read_pid != ipid) seen_accesses.insert(i);
      if (lu >= 0 && i > lu && prefix[lu].iid.get_pid() != last_read_pid+1)
        lu_before_read = true;
    }

    if (lu_before_read) {
      bi.unordered_updates.clear();
      bi.before_unordered.clear();
    } else if(0 <= lu) {
      IPid lu_tipid = prefix[lu].iid.get_pid() & ~0x1;
      if(lu_tipid == ipid && ml != lu_ml && lu != prefix_idx){
        add_happens_after(prefix_idx, lu);
      }

      sym_ty &lu_sym = prefix[lu].sym;
      if (lu_sym.size() != 1
          || lu_sym[0].kind != SymEv::RMW
          || !rmwaction_commutes(conf, lu_sym[0].rmw_kind(),
                                 lu_sym[0].rmw_result_used(),
                                 action.kind, action.result_used)
          || lu_sym[0].addr() != ml) {
        conflicts_with_lu = true;
        observe_memory(b, bi, seen_accesses, seen_pairs, true);
      } else {
        seen_accesses.insert(bi.before_unordered);
      }
    }
    /* Register access in memory */
    assert(!conflicts_with_lu || bi.unordered_updates.empty());
    bi.unordered_updates[ipid] = prefix_idx;
    bi.last_update = prefix_idx;
    bi.last_update_ml = ml;
    wakeup(Access::W,b);
  }

  seen_accesses.insert(last_full_memory_conflict);

  see_events(seen_accesses);
  see_event_pairs(seen_pairs);

  return true;
}

// bool EventTraceBuilder::xchg_await(const SymData &sd, AwaitCond cond) {
//   if (!record_symbolic(SymEv::XchgAwait(sd, cond))) return false;
//   const SymAddrSize &ml = sd.get_ref();
//   if(dryrun){
//     assert(prefix_idx+1 < int(prefix.len()));
//     assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
//     IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
//     VecSet<SymAddr> &R = threads[pid].sleep_accesses_r;
//     VecSet<SymAddr> &W = threads[pid].sleep_accesses_w;
//     for(SymAddr b : ml){
//       R.insert(b);
//       W.insert(b);
//     }
//     return true;
//   }
//   IPid ipid = curev().iid.get_pid();
//   assert(ipid % 2 == 0);

//   { // Add the clock of the auxiliary thread (because of fence semantics)
//     assert(threads[ipid].store_buffer.empty());
//     add_happens_after_thread(prefix_idx, ipid+1);
//   }

//   VecSet<int> seen_accesses;
//   VecSet<int> &happens_after_later = curev().happens_after_later;
//   VecSet<std::pair<int,int>> seen_pairs;

//   /* Clear it from blocked_awaits, if it is present. */
//   auto it = blocked_awaits.find(ml.addr);
//   if (it != blocked_awaits.end()) {
//     it->second.erase(curev().iid.get_pid());
//     if (it->second.empty()) blocked_awaits.erase(it);
//   }

//   /* See previous updates & reads to ml */
//   for(SymAddr b : ml){
//     ByteInfo &bi = mem[b];
//     int lu = bi.last_update;
//     const SymAddrSize &lu_ml = bi.last_update_ml;
//     bool lu_before_read = false;
//     assert(lu < int(prefix.len()));

//     for(int i : bi.last_read){
//       if(0 <= i && prefix[i].iid.get_pid() != ipid) {
//         /* A lot of these will be redundant. We should consider how to
//          * make this more efficient. */
//         if (awaitcond_satisfied_before(i, ml, cond)) {
//           seen_accesses.insert(i);
//         } else {
//           happens_after_later.insert(i);
//         }
//       }
//       if (i > lu) lu_before_read = true;
//     }

//     if (lu_before_read) {
//       bi.unordered_updates.clear();
//       bi.before_unordered.clear();
//     } else if(0 <= lu) {
//       IPid lu_tipid = prefix[lu].iid.get_pid() & ~0x1;
//       if(lu_tipid == ipid && ml != lu_ml && lu != prefix_idx){
//         add_happens_after(prefix_idx, lu);
//       }

//       observe_memory(b, bi, happens_after_later, seen_pairs, true);
//     }
//     /* Register access in memory */
//     assert(bi.unordered_updates.empty());
//     bi.unordered_updates[ipid] = prefix_idx;
//     bi.last_update = prefix_idx;
//     bi.last_update_ml = ml;
//     wakeup(Access::W,b);
//   }

//   happens_after_later.insert(last_full_memory_conflict);

//   see_events(seen_accesses);
//   see_event_pairs(seen_pairs);
//   return true;
// }

// bool EventTraceBuilder::xchg_await_fail(const SymData &sd, AwaitCond cond) {
//   if (conf.memory_model != Configuration::SC) {
//     invalid_input_error("Exchange-Await is only implemented for SC right now");
//     return false;
//   }
//   assert(!dryrun);

//   auto iid = curev().iid;
//   SymEv e = SymEv::XchgAwait(sd, std::move(cond));
//   const SymAddrSize &ml = sd.get_ref();
//   auto ret = blocked_awaits[ml.addr].try_emplace
//     (iid.get_pid(), iid.get_index(), std::move(e));
// #ifndef NDEBUG
//   if(!ret.second) {
//     BlockedAwait &aw = ret.first->second;
//     assert(aw.index == curev().iid.get_index());
//     const AwaitCond &one = e.cond();
//     const AwaitCond &other = aw.ev.cond();
//     assert(other.op == one.op);
//     assert(memcmp(other.operand.get(), one.operand.get(), ml.size) == 0);
//   }
// #endif

//   /* We postpone race detection of failed awaits until the end, in case
//    * they get unblocked. */

//   return true;
// }

bool EventTraceBuilder::load(const SymAddrSize &ml){
  if (!record_symbolic(SymEv::Load(ml))) return false;
  do_load(ml);
  return true;
}

void EventTraceBuilder::do_load(const SymAddrSize &ml){
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = SPS.get_pid(prefix[prefix_idx+1].sleep[dry_sleepers-1]);
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
  VecSet<std::pair<int,int>> seen_pairs;

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
    observe_memory(b, mem[b], seen_accesses, seen_pairs, false);

    /* Register load in memory */
    mem[b].last_read[ipid/2] = prefix_idx;
    wakeup(Access::R,b);
  }

  seen_accesses.insert(last_full_memory_conflict);

  see_events(seen_accesses);
  see_event_pairs(seen_pairs);
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

// bool EventTraceBuilder::load_await(const SymAddrSize &ml, AwaitCond cond) {
//   if (conf.memory_model != Configuration::SC) {
//     invalid_input_error("Load-Await is only implemented for SC right now");
//     return false;
//   }
//   if (!record_symbolic(SymEv::LoadAwait(ml, cond))) return false;

//   if (dryrun) {
//     assert(prefix_idx+1 < int(prefix.len()));
//     assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
//     IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
//     VecSet<SymAddr> &A = threads[pid].sleep_accesses_r;
//     for(SymAddr b : ml){
//       A.insert(b);
//     }
//     return true;
//   }
//   IPid ipid = curev().iid.get_pid();
//   assert(threads[ipid].store_buffer.empty());

//   VecSet<int> &happens_after_later = curev().happens_after_later;
//   VecSet<std::pair<int,int>> seen_pairs;

//   /* Clear it from blocked_awaits, if it is present. */
//   auto it = blocked_awaits.find(ml.addr);
//   if (it != blocked_awaits.end()) {
//     it->second.erase(curev().iid.get_pid());
//     if (it->second.empty()) blocked_awaits.erase(it);
//   }

//   for (SymAddr b : ml) {
//     ByteInfo &bi = mem[b];
//     observe_memory(b, bi, happens_after_later, seen_pairs, false);

//     /* Register load in memory */
//     mem[b].last_read[ipid/2] = prefix_idx;
//     wakeup(Access::R,b);
//   }

//   see_event_pairs(seen_pairs);
//   return true;
// }

// bool EventTraceBuilder::load_await_fail(const SymAddrSize &ml, AwaitCond cond) {
//   if (conf.memory_model != Configuration::SC) {
//     invalid_input_error("Load-Await is only implemented for SC right now");
//     return false;
//   }
//   assert(!dryrun);

//   auto iid = curev().iid;
//   SymEv ev(SymEv::LoadAwait(ml, std::move(cond)));
//   auto ret = blocked_awaits[ml.addr].try_emplace
//     (iid.get_pid(), iid.get_index(), std::move(ev));
// #ifndef NDEBUG
//   if(!ret.second) {
//     BlockedAwait &aw = ret.first->second;
//     assert(aw.index == curev().iid.get_index());
//     const AwaitCond &one = ev.cond();
//     const AwaitCond &other = aw.ev.cond();
//     assert(other.op == one.op);
//     assert(memcmp(other.operand.get(), one.operand.get(), ml.size) == 0);
//   }
// #endif

//   /* We postpone race detection of failed awaits until the end, in case
//    * they get unblocked. */

//   return true;
// }

// static bool shadows_all_of(const sym_ty &sym, const SymAddrSize &ml) {
//   VecSet<SymAddr> addrs(ml.begin(), ml.end());
//   for (const SymEv &e : sym) {
//     /* Only some event kinds shadows */
//     if (e.kind == SymEv::FULLMEM) return true; // Probably unreachable
//     if (e.kind != SymEv::STORE && e.kind != SymEv::FULLMEM
//         && e.kind != SymEv::XCHG_AWAIT) continue;
//     for (SymAddr a : e.addr()) addrs.erase(a);
//     if (addrs.empty()) return true;
//   }

//   assert(!addrs.empty());
//   return false;
// }

// bool EventTraceBuilder::do_await(unsigned j, const IID<IPid> &iid, const SymEv &e,
//                                const VClock<IPid> &above_clock,
//                                std::vector<Race> &races) {
//   bool can_stop = false;
//   const SymAddrSize &ml = e.addr();
//   const AwaitCond &cond = e.cond();
//   std::vector<unsigned> unordered_accesses;
//   for (unsigned i = j;;) {
//     if (i-- == 0) break;
//     const Event &ie = prefix[i];
//     if (std::any_of(ie.sym.begin(), ie.sym.end(),
//                     [](const SymEv &e) { return e.kind == SymEv::FULLMEM; })) {
//       invalid_input_error
//         ("Full memory conflicts are not compatible with awaits", get_iid(i));
//       return false;
//     }
//     if (!std::any_of(ie.sym.begin(), ie.sym.end(),
//                      [&ml](const SymEv &e) { return symev_does_store(e)
//                          && e.addr().overlaps(ml); })) {
//       continue;
//     }
//     can_stop = can_stop || shadows_all_of(ie.sym, ml);
//     if (conf.commute_rmws) {
//       // Optimisation idea: Don't include a set of k's that shadow i
//       if (unordered_accesses.size() >= 20)
//         Debug::warn("EventTracebuilder::do_await:exponential")
//           << "WARNING: Scaling exponentially on a large number of independent writes\n";
//       const auto &not_excluded = [this](const std::vector<unsigned> &exclude, unsigned e) {
//         const auto &eclock = prefix[e].clock;
//         for (unsigned x : exclude) {
//           if (eclock.includes(prefix[x].iid)) return false;
//         }
//         return true;
//       };
//       /* TODO: Can this be done non-recursively? (maybe by using include
//        * and exclude as the state somehow?) */
//       std::vector<unsigned> include; include.reserve(unordered_accesses.size());
//       std::vector<unsigned> exclude; exclude.reserve(unordered_accesses.size());
//       bool did_insert = false;
//       const std::function<void(unsigned)> try_subsequences = [&](const unsigned k) {
//         if (k == 0) {
//           // Do the do
//           assert(std::is_sorted(include.begin(), include.end()));
//           if (awaitcond_satisfied_by(i, include, ml, cond)) {
//             if (conf.debug_print_on_reset) {
//               llvm::dbgs() << "Yes, I can reverse " << i << iid_string(i) << " with "
//                            << j << (j != prefix.len() ? iid_string(j) : "b")
//                            << "\ninc: [";
//               for (unsigned i : include) llvm::dbgs() << i << iid_string(i) << ", ";
//               llvm::dbgs() << "] exc: [";
//               for (unsigned i : exclude) llvm::dbgs() << i << iid_string(i) << ", ";
//               llvm::dbgs() << "]\n";
//             }
//             races.push_back(Race::Sequence(i, j, iid, e, exclude)); // XXX
//             did_insert = true;
//           }
//           return;
//         } else {
//           const unsigned ke = unordered_accesses[k-1];
//           if (prefix[ke].clock.includes(ie.iid)) { //  ie.clock.includes(prefix[ke].iid))
//             /* ke is not in notdep(i) */
//             try_subsequences(k-1);
//             return;
//           }
//           if (!(above_clock.includes(prefix[ke].iid))) {
//             exclude.push_back(ke);
//             try_subsequences(k-1);
//             assert(exclude.back() == ke);
//             exclude.pop_back();
//           }
//           if (not_excluded(exclude, ke)) {
//             include.push_back(ke);
//             try_subsequences(k-1);
//             assert(include.back() == ke);
//             include.pop_back();
//           }
//         }
//       };
//       if (!above_clock.includes(ie.iid)) {
//         try_subsequences(unordered_accesses.size());
//       }
//       unordered_accesses.push_back(i);
//       if (can_stop && did_insert) break;
//     } else if (above_clock.includes(ie.iid)) {
//       continue;
//     } else if (awaitcond_satisfied_before(i, ml, cond)) {
//       if (conf.debug_print_on_reset) {
//         llvm::dbgs() << "Yes, I can reverse " << i << iid_string(i) << " with " << j << (j != prefix.len() ? iid_string(j) : "b") << "\n";
//       }
//       races.push_back(Race::Sequence(i, j, iid, e, {}));
//       if (can_stop) break;
//     }
//   }
//   return true;
// }

bool EventTraceBuilder::full_memory_conflict(){
  if (!record_symbolic(SymEv::Fullmem())) return false;
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = SPS.get_pid(prefix[prefix_idx+1].sleep[dry_sleepers-1]);
    threads[pid].sleep_full_memory_conflict = true;
    return true;
  }

  /* See all previous memory accesses */
  VecSet<int> seen_accesses;
  VecSet<std::pair<int,int>> seen_pairs;
  for(auto it = mem.begin(); it != mem.end(); ++it){
    observe_memory(it->first, it->second, seen_accesses, seen_pairs, true);
    it->second.before_unordered = {prefix_idx}; // Not needed?
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
  see_event_pairs(seen_pairs);
  return true;
}

static bool observe_store(sym_ty &syms, const SymAddr &ml) {
  for (auto it = syms.end();;){
    assert(it != syms.begin());
    --it;
    if((it->kind == SymEv::STORE || it->kind == SymEv::RMW
        || it->kind == SymEv::CMPXHG || it->kind == SymEv::XCHG_AWAIT)
       && it->addr().includes(ml)) break;
    if (it->kind == SymEv::UNOBS_STORE && it->addr().includes(ml)) {
      *it = SymEv::Store(it->data());
      return true;
    }
    assert(!symev_does_store(*it) || !it->addr().includes(ml));
  }
  return false;
}

static void add_to_seen
(boost::container::flat_map<int, unsigned> &unordered_updates,
 VecSet<int> &seen_accesses) {
  std::vector<int> es;
  es.reserve(unordered_updates.size());
  for (auto &u : unordered_updates) {
    es.push_back(u.second);
  }
  std::sort(es.begin(), es.end());
  seen_accesses.insert(VecSet<int>(std::move(es)));
}

void EventTraceBuilder::observe_memory(SymAddr ml, ByteInfo &m,
                                     VecSet<int> &seen_accesses,
                                     VecSet<std::pair<int,int>> &seen_pairs,
                                     bool is_update){
  IPid ipid = curev().iid.get_pid();
  int lu = m.last_update;
  const SymAddrSize &lu_ml = m.last_update_ml;
  if(0 <= lu){
    IPid lu_tipid = prefix[lu].iid.get_pid() & ~0x1;
    if(lu_tipid != ipid){
      seen_accesses.insert(lu);
      //currtrace.emplace(prefix[lu].iid, curev().iid);
    }
    bool did_observe_store = false;
    if (conf.dpor_algorithm == Configuration::OBSERVERS) {
      /* Update last_update to be an observed store */
      did_observe_store = observe_store(prefix[lu].sym, ml);
      if (did_observe_store) {
        /* Add races */
        for (const std::pair<IPid,unsigned> &u : m.unordered_updates) {
          if (u.second != unsigned(lu)) {
            seen_pairs.insert(std::pair<int,int>(u.second, lu));
          }
        }
        m.unordered_updates.clear();
        m.before_unordered = {lu};
      }
    }
    if (!did_observe_store) {
      if (is_update) {
        m.before_unordered = to_vecset_and_clear(m.unordered_updates);
        if (m.before_unordered.empty() && lu >= 0) {
          m.before_unordered = {lu};
        }
        seen_accesses.insert(m.before_unordered);
      } else {
        add_to_seen(m.unordered_updates, seen_accesses);
      }
    } else {
      assert(m.unordered_updates.size() == 0);
    }
  }
  assert(!is_update || m.unordered_updates.size() == 0);
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
  if (!record_symbolic(SymEv::Join(threads[tgt_proc*2].spid)))
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
    IPid pid = SPS.get_pid(prefix[prefix_idx+1].sleep[dry_sleepers-1]);
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
    IPid pid = SPS.get_pid(prefix[prefix_idx+1].sleep[dry_sleepers-1]);
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
    IPid pid = SPS.get_pid(prefix[prefix_idx+1].sleep[dry_sleepers-1]);
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
    IPid pid = SPS.get_pid(prefix[prefix_idx+1].sleep[dry_sleepers-1]);
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
    IPid pid = SPS.get_pid(prefix[prefix_idx+1].sleep[dry_sleepers-1]);
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
    IPid pid = SPS.get_pid(prefix[prefix_idx+1].sleep[dry_sleepers-1]);
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
    IPid pid = SPS.get_pid(prefix[prefix_idx+1].sleep[dry_sleepers-1]);
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
    IPid pid = SPS.get_pid(prefix[prefix_idx+1].sleep[dry_sleepers-1]);
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

bool EventTraceBuilder::cond_wait(const SymAddrSize &cond_ml,
				  const SymAddrSize &mutex_ml){
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
    if(!dryrun && (mtx.last_lock < 0 ||
		   prefix[mtx.last_lock].iid.get_pid() !=
		   curev().iid.get_pid())){
      pthreads_error("cond_wait called with mutex which is not locked by the same thread.");
      return false;
    }
  }

  curev().may_conflict = true;
  if (!mutex_unlock(mutex_ml)) return false;
  if (!record_symbolic(SymEv::CWait(cond_ml))) return false;
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = SPS.get_pid(prefix[prefix_idx+1].sleep[dry_sleepers-1]);
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

bool EventTraceBuilder::cond_awake(const SymAddrSize &cond_ml,
				   const SymAddrSize &mutex_ml){
  if (!dryrun){
    assert(cond_vars.count(cond_ml.addr));
    CondVar &cond_var = cond_vars[cond_ml.addr];
    add_happens_after(prefix_idx, cond_var.last_signal);
  }

  curev().may_conflict = true;
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
    IPid pid = SPS.get_pid(prefix[prefix_idx+1].sleep[dry_sleepers-1]);
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
				      sleep_trees_t &sleep_trees,
				      const Event &e,
				      const std::vector<bool> &handler_busy) const{
  for (int k = 0; k < e.sleep.size(); ++k){
    sleep.sleep.push_back({e.sleep[k], &e.sleep_evs[k], nullptr});
  }
  for(auto p : e.sleep_trees){
    IPid handler = threads[SPS.get_pid(p.first)].handler_id;
    sleep_trees.push_back(sleep_tree{p.first, 0, std::vector<VClock<IPid>>(),
				     p.second, handler_busy});
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
EventTraceBuilder::obs_sleep_wake(struct obs_sleep &sleep,
				  sleep_trees_t &sleep_trees,
				  const Event &e,
				  bool multiple_handlers) const{
#ifndef NDEBUG
    obs_wake_res res =
#endif
      obs_sleep_wake(sleep, sleep_trees, threads[e.iid.get_pid()].spid,
		     e.iid.get_index(), e.clock, e.sym, multiple_handlers);
    assert(res != obs_wake_res::BLOCK);
}

static bool symev_does_load(const SymEv &e) {
  return e.kind == SymEv::LOAD || e.kind == SymEv::CMPXHG
    || e.kind == SymEv::CMPXHGFAIL || e.kind == SymEv::FULLMEM;
}

void EventTraceBuilder::
update_witness_sets(unsigned index, bool end_of_msg, IPid handler,
		    const VClock<IPid> &clock,
		    sleep_trees_t &sleep_trees,
		    std::vector<std::vector<bool>>
		    &busy_n_hap_aft_witness) const{
  /* If there is a message, first half of which is in the prefix and
   * the rest is in the WS, the later messages from the same handler
   * cannot be moved before this message. So this message is a
   * potential witness for clearing a message from the sleepset.
   */
  if(handler != -1){
    if(index == 1){
      for(auto &slp_tree : sleep_trees){
	if(handler == threads[SPS.get_pid(slp_tree.spid)].handler_id)
	  slp_tree.witness_events.push_back(clock);
	if(busy_n_hap_aft_witness[slp_tree.spid][handler])
	  slp_tree.witness_events.push_back(clock);
      }
    } else if(end_of_msg){
      for(auto &slp_tree : sleep_trees)
	for(auto e : slp_tree.witness_events)
	  if(slp_tree.handler_busy[handler] && e.lt(clock))
	    busy_n_hap_aft_witness[slp_tree.spid][handler] = true;
    }
  }
}

EventTraceBuilder::obs_wake_res EventTraceBuilder::
obs_sleep_wake(struct obs_sleep &sleep, sleep_trees_t &sleep_trees, IPid p,
	       unsigned index, VClock<IPid> clock, const sym_ty &sym,
	       bool multiple_handlers) const{
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

  for(auto slp_tree_it = sleep_trees.begin(); slp_tree_it != sleep_trees.end();){
    unsigned handler = threads[SPS.get_pid(slp_tree_it->spid)].handler_id;
    if(slp_tree_it->spid == p){
      // TODO: Block according to the definition of the paper
      // Check till the end of the message(might need to extend the WS
      bool partial_msg = true;
      for(const SymEv &symev : sym) if(symev.is_return()) partial_msg = false;
      if(!slp_tree_it->witness_events.empty() &&
      	 partial_msg){
	//TODO: Delete sequences from the sleep tree that are not matching
	for(const SymEv &symev : sym){
	  if(symev.access_global()) slp_tree_it->start_index++;
	}
	slp_tree_it++;
	continue;
      }
      else if(!multiple_handlers || reordering_possible())
	return obs_wake_res::BLOCK;
    }
    Branch first_ev = slp_tree_it->msg_trails.begin()->front();
    if(slp_tree_it->start_index == 0 && first_ev.index == 1 &&
       do_events_conflict(p, sym, first_ev.spid, first_ev.sym)){
      slp_tree_it = sleep_trees.erase(slp_tree_it);
      continue;
    }
    if(slp_tree_it->witness_events.empty()){
      slp_tree_it++;
      continue;
    }
    for(auto we : slp_tree_it->witness_events){
      if(we.leq(clock)){
      	for(auto seq_it = slp_tree_it->msg_trails.begin();
      	    seq_it != slp_tree_it->msg_trails.end();){
      	  unsigned ind = 0;
      	  bool conflict = false;
      	  for(auto br_it = seq_it->begin();
      	      br_it != seq_it->end(); br_it++, ind++){
      	    if(slp_tree_it->start_index <= ind){
      	      if(do_events_conflict(p, sym, br_it->spid, br_it->sym)){
      	        conflict = true;
      	        break;
      	      }
      	    }
      	  }
      	  if(conflict) seq_it = slp_tree_it->msg_trails.erase(seq_it);
      	  else seq_it++;
      	}
      	break;
      }
    }
    if(slp_tree_it->msg_trails.empty()) slp_tree_it = sleep_trees.erase(slp_tree_it);
    else slp_tree_it++;
  }

  /* Check if the sleep set became empty */
  if (sleep.sleep.empty() && sleep.must_read.empty() &&
      sleep_trees.empty()) {//sleeping_msgs.empty()
    // TODO: Change the condition for obs_wake_res::CLEAR
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
                      const struct obs_sleep &sleep_const,
		      const sleep_trees_t &sleep_trees,
		      std::vector<std::vector<bool>>
                      busy_n_hap_aft_witness) const{
  /* We need a writable copy */
  struct obs_sleep isleep = sleep_const;
  sleep_trees_t slp_trees = sleep_trees;
  obs_wake_res state = obs_wake_res::CONTINUE;
  bool multiple_handlers = false;
  IPid last_handler = -1;
  for (auto it = seq.cbegin(); state == obs_wake_res::CONTINUE
         && it != seq.cend(); ++it) {
    unsigned index = it->index;
    IPid handler = threads[SPS.get_pid(it->spid)].handler_id;
    VClock<IPid> clock = it->clock;
    if(!multiple_handlers && handler != -1){
      if(last_handler != -1 && handler != last_handler)
	multiple_handlers = true;
      last_handler = handler;
    }
    update_witness_sets(it->index, it->is_ret_stmt(),
    			threads[SPS.get_pid(it->spid)].handler_id,
    			it->clock, slp_trees, busy_n_hap_aft_witness);

    state = obs_sleep_wake(isleep, slp_trees, it->spid, it->index,
			   it->clock, it->sym, multiple_handlers);
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
    case SymEv::RMW:
    case SymEv::CMPXHG:
    case SymEv::XCHG_AWAIT:
      assert(symev_does_store(p));
      if (data.get_ref().overlaps(p.addr())) {
        for (SymAddr a : p.addr()) {
          if (needed.erase(a)) {
            data[a] = p.data()[a];
          }
        }
      }
      break;
    default:
      assert(!symev_does_store(p));
      break;
    }
  }
}

// template <class Iter>
// static void recompute_scan_rev
// (const SymAddrSize &desired, VecSet<SymAddr> &needed, std::vector<const SymEv*> &stack,
//  Iter end, Iter begin){
//   for (auto pi = end; !needed.empty() && (pi != begin);){
//     const SymEv &p = *(--pi);
//     switch(p.kind){
//     case SymEv::STORE:
//     case SymEv::UNOBS_STORE:
//     case SymEv::CMPXHG:
//     case SymEv::XCHG_AWAIT: {
//       assert(symev_does_store(p));
//       const SymAddrSize &sas = p.addr();
//       if (desired.overlaps(sas)) {
//         bool any = false;
//         for (SymAddr a : sas) {
//           if (needed.erase(a)) {
//             any = true;
//           }
//         }
//         if (any) stack.push_back(&p);
//       }
//     } break;
//     case SymEv::RMW: {
//       const SymAddrSize &sas = p.addr();
//       if (desired.overlaps(sas)
//           && std::any_of(sas.begin(), sas.end(),
//                          [&](const SymAddr a) { return needed.count(a); })) {
//         assert(sas.subsetof(desired));
//         needed.insert(VecSet<SymAddr>(sas.begin(), sas.end()));
//         stack.push_back(&p);
//       }
//     } break;
//     default:
//       assert(!symev_does_store(p));
//       break;
//     }
//   }
// }

// static void recompute_replay_fwd
// (SymData &data, std::vector<const SymEv*> &stack){
//   while(!stack.empty()) {
//     const SymEv &p = *stack.back();
//     stack.pop_back();
//     const SymAddrSize &sas = p.addr();
//     if (p.kind == SymEv::RMW) {
//       assert(sas.subsetof(data.get_ref()));
//       void *data_at_sas = (char*)data.get_block() + (sas.addr - data.get_ref().addr);
//       p.rmwaction().apply_to(data_at_sas, sas.size, data_at_sas);
//     } else {
//       assert(symev_does_store(p));
//       assert(data.get_ref().overlaps(sas));
//       for (SymAddr a : sas) {
//         data[a] = p.data()[a];
//       }
//     }
//   }
// }

// bool EventTraceBuilder::awaitcond_satisfied_before
// (unsigned i, const SymAddrSize &ml, const AwaitCond &cond) const {
//   /* Recompute what's written */
//   SymData data(ml, ml.size);
//   VecSet<SymAddr> needed(ml.begin(), ml.end());
//   std::memset(data.get_block(), 0, ml.size);

//   for (unsigned j = i; !needed.empty();) {
//     if (j-- == 0) break;
//     const sym_ty &js = prefix[j].sym;
//     rev_recompute_data(data, needed, js.end(), js.begin());
//   }

//   return cond.satisfied_by(data);
// }

// bool EventTraceBuilder::awaitcond_satisfied_by
// (unsigned i, const std::vector<unsigned> &seq, const SymAddrSize &ml,
//  const AwaitCond &cond) const {
//   /* Recompute what's written */
//   SymData data(ml, ml.size);
//   VecSet<SymAddr> needed(ml.begin(), ml.end());
//   std::memset(data.get_block(), 0, ml.size);
//   std::vector<const SymEv*> stack;

//   /* Last comes seq */
//   for (unsigned j = seq.size(); !needed.empty();) {
//     if (j-- == 0) break;
//     const sym_ty &js = prefix[seq[j]].sym;
//     recompute_scan_rev(ml, needed, stack, js.end(), js.begin());
//   }

//   /* Then comes then prefix[:i] */
//   for (unsigned j = i; !needed.empty();) {
//     if (j-- == 0) break;
//     const sym_ty &js = prefix[j].sym;
//     recompute_scan_rev(ml, needed, stack, js.end(), js.begin());
//   }

//   recompute_replay_fwd(data, stack);

//   return cond.satisfied_by(data);
// }

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
        else
	  last_reads.insert(VecSet<SymAddr>(e.addr().begin(), e.addr().end()));
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
        else
	  last_reads.erase (VecSet<SymAddr>(e.addr().begin(), e.addr().end()));
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
  // for(auto i : seen_accesses)
    IPid fst_pid = prefix[i].iid.get_pid();
    IPid snd_pid = curev().iid.get_pid();
    if(threads[fst_pid].handler_id != -1 &&
       threads[fst_pid].handler_id == threads[snd_pid].handler_id){
      if (prefix[i].iid.get_pid() == prefix[prefix_idx].iid.get_pid()) continue;
      add_msgrev_race(i);
    }
    else add_noblock_race(i);
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

void EventTraceBuilder::add_msgrev_race(int fst_conflict){
  int first=threads[prefix[fst_conflict].iid.get_pid()].event_indices.front();
  int second=threads[curev().iid.get_pid()].event_indices.front();
  assert(0 <= first);
  assert(first < second);
  assert(second <= prefix_idx);
  assert(do_events_conflict(fst_conflict, prefix_idx));
  for(auto r : prefix[second].races)
    if(r.first_event == first) return;
  prefix[second].races.push_back(Race::MsgRev(first,second,fst_conflict,prefix_idx));
}

void EventTraceBuilder::add_happens_after(unsigned second, unsigned first){
  assert(first != ~0u);
  assert(second != ~0u);
  assert(first != second);
  assert(first < second);
  assert((int_fast64_t)second <= prefix_idx);

  std::vector<unsigned> &vec = prefix[second].happens_after;
  if (vec.size() && vec.back() == first) return;

  vec.push_back(first);
}

void EventTraceBuilder::add_happens_after_thread(unsigned second, IPid thread){
  assert((int_fast64_t)second == prefix_idx);
  if (threads[thread].event_indices.empty()) return;
  add_happens_after(second, threads[thread].event_indices.back());
}

void EventTraceBuilder::add_eom(unsigned second, unsigned first){
  assert(first != ~0u);
  assert(second != ~0u);
  assert(first != second);
  assert(first < second);
  assert((long long)second <= prefix_idx);

  std::set<unsigned> &eoms = prefix[second].eom_before;
  eoms.insert(first);
}

/* Filter the sequence first..last from all elements that are less than
 * any other item. The sequence is modified in place and an iterator to
 * the position beyond the last included element is returned.
 *
 * Assumes less is transitive and asymmetric (a strict partial order)
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
//           |--------|
//[aaaaaaa][bbbbbb][ccccccc]   eom is not transitive in this case
//   |__________|
void EventTraceBuilder::compute_eom(){
  for(IPid i = 2; i<threads.size(); i=i+2){//eom order
    if(threads[i].handler_id == -1) continue;
    for(IPid j = 2; j<threads.size(); j=j+2){
      if(threads[i].handler_id != threads[j].handler_id) continue;
      unsigned fev_i = threads[i].event_indices.front();
      unsigned lev_i = threads[i].event_indices.back();
      unsigned fev_j = threads[j].event_indices.front();
      unsigned lev_j = threads[j].event_indices.back();
      if(fev_j<=fev_i) continue;
      if(prefix[fev_i].clock.lt(prefix[lev_j].clock)){
        add_eom(fev_j,lev_i);
      }
    }
  }
}

void EventTraceBuilder::clear_vclocks(){
  for(int i=0;i<prefix.len();i++)
    prefix[i].clock = VClock<int>();
  has_vclocks = false;
}

void EventTraceBuilder::compute_vclocks(){
  /* Be idempotent */
  if (has_vclocks) return;

  /* The first event of a thread happens after the spawn event that
   * created it.
   */
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
  unsigned last_handler = -1;
  bool multiple_handlers=false;    
  for (unsigned i = 0; i < prefix.len();){
    IPid ipid = prefix[i].iid.get_pid();
    /* Detect multiple handlers */
    if(!multiple_handlers && threads[ipid].handler_id != -1){
      if(last_handler != -1 && threads[ipid].handler_id != last_handler)
	multiple_handlers = true;
      last_handler = threads[ipid].handler_id;
    }
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

    for(unsigned ei : prefix[i].eom_before)
      prefix[i].clock += prefix[ei].clock;
    //Compute eom and backtrack
    if(threads[ipid].handler_id != -1 && i == threads[ipid].event_indices.back()){
      bool backtrack=false;
      unsigned fev_i = threads[ipid].event_indices.front();
      for(IPid j = 2; j<threads.size(); j=j+2){
	if(threads[j].event_indices.empty()) continue;
	if(threads[ipid].handler_id != threads[j].handler_id) continue;
	unsigned fev_j = threads[j].event_indices.front();
	unsigned lev_j = threads[j].event_indices.back();
	if(fev_i <= fev_j) continue;
	if(prefix[fev_i].eom_before.find(lev_j)!=
	   prefix[fev_i].eom_before.end()) continue;
	bool ipid_after_j = false;
	unsigned last = 0;
	for(unsigned k : threads[ipid].event_indices){
	  if(last == k) continue;
	  else last = k;
	  for(Race r : prefix[k].races){
	    if(r.first_event > threads[j].event_indices.front() &&
	       prefix[r.first_event].iid.get_pid() != ipid &&
	       prefix[r.first_event].iid.get_pid() != j &&
	       prefix[threads[j].event_indices.front()].clock.lt
	       (prefix[r.first_event].clock)){
	      ipid_after_j = true;
	    }
	  }
	  for(unsigned ei : prefix[k].happens_after){
	    if(ei > threads[j].event_indices.front() &&
	       prefix[ei].iid.get_pid() != ipid &&
	       prefix[ei].iid.get_pid() != j &&
	       prefix[threads[j].event_indices.front()].clock.lt
	       (prefix[ei].clock)){
	      ipid_after_j = true;
	    }
	  }
	}
	if(ipid_after_j){
	  backtrack=true;
	  add_eom(fev_i,lev_j);
	}
	/* Optimization that finds zigzag patterns of indirect dependency */
	else if(multiple_handlers){
	  std::vector<std::set<unsigned>> msgs_haft_j(threads.size());
	  std::vector<std::set<unsigned>> msgs_hbef_i(threads.size());
	  std::vector<bool> msg_aftj_n_befi(threads.size(),false);
	  for(IPid k = 2; k<threads.size(); k=k+2){
	    if(threads[k].handler_id == -1 || k==i || k==j ||
	       threads[k].event_indices.empty()) continue; 
	    unsigned fev_k = threads[k].event_indices.front();
	    unsigned lev_k = threads[k].event_indices.back();
	    bool after_j=false, before_i=false;
	    if(prefix[fev_k].clock.lt(prefix[i].clock)){
	      before_i=true;
	      msgs_hbef_i[threads[k].handler_id].insert(k);
	    }
	    if(prefix[fev_j].clock.lt(prefix[lev_k].clock)){
	      after_j=true;
	      msgs_haft_j[threads[k].handler_id].insert(k);
	    }
	    if(after_j && before_i){
	      if(msg_aftj_n_befi[threads[k].handler_id]){
		ipid_after_j=true;
		break;
	      } else msg_aftj_n_befi[threads[k].handler_id]=true;
	    }
	  }
	  if(ipid_after_j){
	    backtrack=true;
	    add_eom(fev_i,lev_j);
	  }
	}
      }
      if(backtrack){
	i=fev_i-1;
	continue;
      }
    }
    /* Now we want add the possibly reversible edges, but first we must
     * check for reversibility, since this information is lost (more
     * accurately less easy to compute) once we add them to the clock.
     */
    std::vector<Race> &races = prefix[i].races;
    // for(Race race : races)
    //   llvm::dbgs()<<"Race (<"<<threads[prefix[race.first_event].iid.get_pid()].cpid<<","
    // 	      <<prefix[race.first_event].iid.get_index()<<">,<"
    // 	      <<threads[prefix[race.second_event].iid.get_pid()].cpid
    // 	      <<prefix[race.second_event].iid.get_index()<<">)\n";/////////
    // /* Generate await races (with stores, races with loads are handled eagerly) */
    // if (std::any_of(prefix[i].sym.begin(), prefix[i].sym.end(),
    //                 [](const SymEv &e) { return e.has_cond(); })) {
    //   const SymEv &aw = prefix[i].sym[0];
    //   assert(prefix[i].sym.size() == 1);
    //   do_await(i, prefix[i].iid, aw, prefix[i].clock, races);
    // }
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
        end = partition
          (first_pair, end,
           [this,i](const Race &r){
	     return !prefix[r.first_event].clock.leq(prefix[i].clock);
           });
      for (auto it = end; it != oldend; ++it){
        if (it->kind == Race::LOCK_SUC){
          prefix[i].clock += prefix[it->unlock_event].clock;
	  add_happens_after(i, it->unlock_event);
	  changed = true;
        } else if (it->kind == Race::MSG_REV){
	  int last_of_fst = threads[prefix[it->first_event].iid.get_pid()].
	    event_indices.back();
          prefix[i].clock += prefix[last_of_fst].clock;
	  add_happens_after(i, last_of_fst);
	  changed = true;
        } else{
	  for (const SymEv &fe : prefix[it->first_event].sym)
	    for (const SymEv &se : prefix[it->second_event].sym)
	      if(do_symevs_conflict(it->first_event, fe, it->second_event, se))
		add_happens_after(it->second_event, it->first_event);
	}
      }
    } while (changed);
    /* Then filter out subsumed */
    auto fill = frontier_filter
      (first_pair, end,
       [this](const Race &f, const Race &s){
	 /* return: Does s subsume f? */
	 /* A virtual event does not contribute to the vclock and cannot
	  * subsume races. */
	 if (s.kind == Race::LOCK_FAIL) return false;
	 /* Sequence races can subsume each other, but that is */
        // XXX: Not implemented
        // if (s.kind == Race::SEQUENCE) {
        //   assert(f.kind == Race::SEQUENCE || f.kind == Race::NONBLOCK);
        //   int fe = f.first_event, se = s.first_event;
        //   const std::vector<unsigned> &fx = f.exclude, &sx = s.exclude;
        //   assert(std::is_sorted(fx.begin(), fx.end()));
        //   assert(std::is_sorted(sx.begin(), sx.end()));
        //   if (!prefix[se].clock.includes(prefix[fe].iid)) return false;
        //   /* fe h-b se */

        //   for (auto si = sx.begin(), fi = fx.begin(); si != sx.end(); ++si) {
        //     while (fi != fx.end() && *fi < *si) { ++fi; }
        //     if (fi != fx.end() && *fi == *si) { ++fi; continue; }
        //     if (prefix[*si].clock.includes(prefix[fe].iid)) continue;
        //     return false;
        //   }
        //   return true;
        // }

	 /* Also filter out observed races with nonfirst witness */
	 if (f.kind == Race::OBSERVED && s.kind == Race::OBSERVED
	     && f.first_event == s.first_event
	     && f.second_event == s.second_event){
	   /* N.B. We want the _first_ observer as the witness; thus
	    * the reversal of f and s.
	    */
	   return s.witness_event <= f.witness_event;
	 }
	 int last_of_s = threads[prefix[s.first_event].iid.get_pid()].event_indices.back();
	 int se = s.kind == Race::LOCK_SUC ? s.unlock_event :
	   Race::MSG_REV ? last_of_s : s.first_event;
	 return prefix[f.first_event].clock.leq(prefix[se].clock);
       });
    for(auto it = fill; it != end; ++it){
        for (const SymEv &fe : prefix[it->first_event].sym)
	  for (const SymEv &se : prefix[it->second_event].sym)
	    if(do_symevs_conflict(it->first_event, fe, it->second_event, se))
	      add_happens_after(it->second_event, it->first_event);	      
    }
    /* Add clocks of remaining (reversible) races */
    for (auto it = first_pair; it != fill; ++it){
      if (it->kind == Race::LOCK_SUC){
        assert(prefix[it->first_event].clock.leq
               (prefix[it->unlock_event].clock));
        prefix[i].clock += prefix[it->unlock_event].clock;
      }else if (it->kind == Race::MSG_REV){
	int last_of_fst = threads[prefix[it->first_event].iid.get_pid()].
	    event_indices.back();
        assert(prefix[it->first_event].clock.leq
               (prefix[last_of_fst].clock));
        prefix[i].clock += prefix[last_of_fst].clock;
      }else if (it->kind != Race::LOCK_FAIL){
        prefix[i].clock += prefix[it->first_event].clock;
      }
    }
    // assert(prefix[i].happens_after_later.empty()
    //        || (prefix[i].sym.size() == 1
    //            && prefix[i].sym[0].has_cond()));
    // for (int b : prefix[i].happens_after_later) {
    //   if (b != -1 && !prefix[i].clock.includes(prefix[b].iid)) {
    //     prefix[i].clock += prefix[b].clock;
    //   }
    // }
    // prefix[i].happens_after_later.clear();
    /* Now delete the subsumed races. We delayed doing this to avoid
     * iterator invalidation. */
    races.resize(fill - races.begin(), races[0]);
    i++;
  }
  has_vclocks = true;
}

bool EventTraceBuilder::record_symbolic(SymEv event){
  if(dryrun) {
    assert(prefix_idx+1 < int(prefix.len()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = SPS.get_pid(prefix[prefix_idx+1].sleep[dry_sleepers-1]);
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
      auto pid_str = [this](IPid p) {
	return p*2 >= threads.size() ? std::to_string(p)
	  : threads[p*2].cpid.to_string();
      };
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
  return do_events_conflict(prefix[i], prefix[j]);
}

bool EventTraceBuilder::do_events_conflict(const Event &fst,
					   const Event &snd) const{
  return do_events_conflict(threads[fst.iid.get_pid()].spid, fst.sym,
                            threads[snd.iid.get_pid()].spid, snd.sym);
}

static bool symev_has_pid(const SymEv &e) {
  return e.kind == SymEv::SPAWN || e.kind == SymEv::JOIN || e.kind == SymEv::POST;
}

static bool symev_is_load(const SymEv &e) {
  return e.kind == SymEv::LOAD || e.kind == SymEv::CMPXHGFAIL
    || e.kind == SymEv::LOAD_AWAIT;
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
  if (fst.kind == SymEv::RMW && snd.kind == SymEv::RMW
      && fst.addr() == snd.addr()
      && rmwaction_commutes(conf, fst.rmw_kind(), fst.rmw_result_used(),
                            snd.rmw_kind(), snd.rmw_result_used())) {
    return false;
  }

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
  if (threads[s_ipid].handler_id == f_ipid) return true;
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

bool EventTraceBuilder::do_msgs_conflict
(IPid fst_spid, IPid snd_spid) const{
  if(fst_spid == snd_spid) return true;
  IPid fst = SPS.get_pid(fst_spid);
  IPid snd = SPS.get_pid(snd_spid);
  for(unsigned ei : threads[fst].event_indices){
    for(unsigned ej : threads[snd].event_indices){
      if(do_events_conflict(ei,ej)) {
	return true;
      }
    }
  }
  // if(eoms.find(snd) != eoms.end() &&
  //    std::find(eoms.at(snd).begin(), eoms.at(snd).end(), fst) !=
  //    eoms.at(snd).end()) return true;
  // if(eoms.find(fst) != eoms.end() &&
  //    std::find(eoms.at(fst).begin(), eoms.at(fst).end(), snd) !=
  //    eoms.at(fst).end()) return true;
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

std::map<EventTraceBuilder::IPid,
	 std::vector<unsigned>> EventTraceBuilder::
mark_sleepset_clearing_events(std::vector<Branch> &v,
			      struct obs_sleep sleep,
			      sleep_trees_t sleep_trees){
  obs_wake_res state = obs_wake_res::CONTINUE;
  std::map<IPid, std::vector<unsigned>> clear_set;
  for(unsigned i = 0; i < v.size(); i++){
    if(threads[SPS.get_pid(v[i].spid)].handler_id != -1 && v[i].index == 1){
      for(auto &slp_tree : sleep_trees){
	if(threads[SPS.get_pid(v[i].spid)].handler_id
	   == threads[SPS.get_pid(slp_tree.spid)].handler_id)
	  slp_tree.witness_events.push_back(v[i].clock);
      }
    }

    for (unsigned j = 0; j < sleep.sleep.size();) {
      const auto &s = sleep.sleep[j];
      if (s.spid == v[i].spid) {
	unordered_vector_delete(sleep.sleep, j);
      } else if (do_events_conflict(v[i].spid, v[i].sym, s.spid, *s.sym)){
	bool skip = false;
	for(unsigned ei : clear_set[s.spid]){
	  if(do_events_conflict(v[ei].spid, v[ei].sym, v[i].spid, v[i].sym))
	     skip = true; 
	}
	if(!skip) clear_set[s.spid].emplace_back(i);
	++j;
      } else ++j;
    }

    for(auto slp_tree_it = sleep_trees.begin();
    	slp_tree_it != sleep_trees.end();){
      unsigned handler = threads[SPS.get_pid(slp_tree_it->spid)].handler_id;
      if(slp_tree_it->spid == v[i].spid){
    	// TODO: Block according to the definition of the paper
    	slp_tree_it = sleep_trees.erase(slp_tree_it);
	continue;
	bool partial_msg = v[i].is_ret_stmt()? true : false;
	if(!slp_tree_it->witness_events.empty() && partial_msg){
	  for(const SymEv &symev : v[i].sym){
	    if(symev.access_global()) slp_tree_it->start_index++;
	  }
	  slp_tree_it++;
	}
	continue;
      }
      Branch first_ev = slp_tree_it->msg_trails.begin()->front();
      if(slp_tree_it->start_index == 0 && first_ev.index == 1 &&
	 do_events_conflict(v[i].spid, v[i].sym, first_ev.spid, first_ev.sym)){
    	bool skip = false;
    	for(unsigned ei : clear_set[slp_tree_it->spid]){
    	  if(do_events_conflict(v[ei].spid, v[ei].sym, v[i].spid, v[i].sym))
    	     skip = true; 
    	}
    	if(!skip) clear_set[slp_tree_it->spid].emplace_back(i);
	slp_tree_it++;
    	continue;
      }
      if(slp_tree_it->witness_events.empty()){
    	slp_tree_it++;
    	continue;
      }
      for(auto we : slp_tree_it->witness_events){
	if(we.leq(v[i].clock)){
	  for(auto seq_it = slp_tree_it->msg_trails.begin();
	      seq_it != slp_tree_it->msg_trails.end(); seq_it++){
	    unsigned ind = 0;
	    bool conflict = false;
	    for(auto br_it = seq_it->begin();
		br_it != seq_it->end(); br_it++, ind++){
	      if(slp_tree_it->start_index <= ind){
		if(do_events_conflict(v[i].spid, v[i].sym,
				      br_it->spid, br_it->sym)){
		  conflict = true;
		  break;
		}
	      }
	    }
	    if(conflict){
	      bool skip = false;
    	      for(unsigned ei : clear_set[slp_tree_it->spid]){
    		if(do_events_conflict(v[ei].spid, v[ei].sym, v[i].spid, v[i].sym))
    		  skip = true; 
    	      }
    	      if(!skip)
    		clear_set[slp_tree_it->spid].emplace_back(i);
	    }
	  }
	  break;
	}
      }
      slp_tree_it++;
    }
  }
  return clear_set;
}

void EventTraceBuilder::do_race_detect() {
  assert(has_vclocks);
  assert(0 < prefix.len());
  /* Compute all races of blocked awaits. */
  // for (const auto &ab : blocked_awaits) {
  //   for (const auto &pb : ab.second) {
  //     IID<IPid> iid(pb.first, pb.second.index);
  //     std::vector<Race> races;
  //     const SymEv &ev = pb.second.ev;
  //     assert(!try_find_process_event(pb.first, iid.get_index()).first);
  //     VClock<IPid> clock = reconstruct_blocked_clock(iid);
  //     do_await(prefix.len(), iid, ev, clock, races);
  //     for (Race &r : races) {
  //       assert(r.first_event >= 0 && r.first_event < ssize_t(prefix.len()));
  //       /* Can we optimise do_await to not include these guys in the
  //        * first place? */
  //       // XXX: What about other events in include?
  //       assert (!clock.includes(prefix[r.first_event].iid));
  //       lock_fail_races.push_back(std::move(r));
  //     }
  //   }
  // }
  /* Do race detection */
  std::vector<std::vector<std::vector<Branch>>> WSs(prefix.len(), std::vector<std::vector<Branch>>());
  std::map<IPid, std::vector<IPid>> eoms;
  for (const Race &r : lock_fail_races){
    unsigned br_point;
    std::vector<bool> in_notdep(prefix.len());
    Branch second_br(0,0);
    if(!wakeup_sequence(r, br_point, in_notdep, second_br)) continue;
    std::vector<Branch> v =
      linearize_sequence(br_point, second_br, r, in_notdep);
    assert(0 <= br_point && br_point < prefix.len());
    WSs[br_point].push_back(std::move(v));
  }
  for (unsigned i = 0; i < prefix.len(); ++i){
    auto special_case1 = [this](IPid fst_handler, unsigned fst, unsigned sec){
                          VClock<IPid> pre = prefix[sec].clock;
			  IPid snd_handler =
			    threads[prefix[sec].iid.get_pid()].handler_id;
                          for(unsigned k = sec-1; k > fst; k--){
			    IPid pid = prefix[k].iid.get_pid();
			    if(threads[pid].handler_id == snd_handler &&
			       threads[pid].event_indices.back() == k &&
			       threads[pid].event_indices.front() < fst)
			      pre += prefix[k].clock;
			  }
			  for(unsigned k = fst+1; k < sec; k++){
			    IPid pid = prefix[k].iid.get_pid();
			    
			    if(prefix[k].iid.get_index() == 1 &&
			       threads[pid].handler_id == fst_handler &&
			       prefix[k].clock.lt(pre)){
			      return true;
			    }
			  }
			  return false;
			};
    auto special_case2 = [this](IPid handler, unsigned fst, unsigned sec){
			  for(unsigned k = fst+1; k < sec; k++){
			    IPid pid = prefix[k].iid.get_pid();
			    if(threads[pid].handler_id == handler &&
			       threads[prefix[k].iid.get_pid()].event_indices.back() == k &&
			       prefix[fst].clock.lt(prefix[k].clock)){
			      return true;
			    }
			  }
			  return false;
			};
    for (const Race &r : prefix[i].races){
      IPid fpid = prefix[r.first_event].iid.get_pid();
      IPid spid = prefix[r.second_event].iid.get_pid();
      if(r.kind==Race::MSG_REV ||
	 (threads[fpid].handler_id != -1 &&
	  threads[fpid].handler_id != threads[spid].handler_id &&
	  special_case1(threads[fpid].handler_id,r.first_event,r.second_event))){
	unsigned br_point;
	std::vector<bool> in_notdep(prefix.len());
	Branch second_br(0,0);
	if(!wakeup_sequence(r, br_point, in_notdep, second_br)) continue;
	std::vector<Branch> v =
	  linearize_sequence(br_point, second_br, r, in_notdep);
	assert(0 <= br_point && br_point < prefix.len());
	WSs[br_point].push_back(std::move(v));
      }
	      
      else if(threads[fpid].handler_id != -1 &&
	      threads[fpid].handler_id != threads[spid].handler_id &&
	      special_case2(threads[spid].handler_id,r.first_event,r.second_event)){
	continue;
      }
      else{
	unsigned br_point;
	std::vector<bool> in_notdep(prefix.len());
	Branch second_br(0,0);
	if(!wakeup_sequence(r, br_point, in_notdep, second_br)) continue;
	std::vector<Branch> v =
	  linearize_sequence(br_point, second_br, r, in_notdep);
	assert(0 <= br_point && br_point < prefix.len());
	WSs[br_point].push_back(std::move(v));
      }
    }
  }

  /* Insert WSs in the tree */
  struct obs_sleep sleep;
  sleep_trees_t sleep_trees;
  std::vector<bool> handler_busy(SPS.num_of_threads(), false);
  /* The handlers that are in the middle of a execution of a message */
  std::vector<std::vector<bool>>
    busy_n_hap_aft_witness(SPS.num_of_threads(),
			   std::vector<bool>(SPS.num_of_threads(), false));
  bool multiple_handlers = false;
  IPid last_handler = -1;
  std::vector<IPid> ongoing_msg(threads.size(),0);
  for (unsigned i = 0; i < prefix.len(); ++i){
    IPid ipid = prefix[i].iid.get_pid();
    unsigned index = prefix[i].iid.get_index();
    IPid handler = threads[ipid].handler_id;
    if(!multiple_handlers && handler != -1){
      if(last_handler != -1 && handler != last_handler)
	multiple_handlers = true;
      last_handler = handler;
    }
    // llvm::dbgs()<<i<<"\n";//////////////
    obs_sleep_add(sleep, sleep_trees, prefix[i], handler_busy);
    no_of_pending_WSs -= prefix.branch(i).pending_WSs.size();

    /* Insert pending WSs */
    for(auto v_it = prefix.branch(i).pending_WSs.begin();
	v_it != prefix.branch(i).pending_WSs.end();) {
      std::vector<Branch> v = *v_it;
      // llvm::dbgs()<<"Pending: ";/////////////////"
      // for(Branch br:v) llvm::dbgs()<<"("<<threads[SPS.get_pid(br.spid)].cpid<<","<<br.index<<")";////////////
      // llvm::dbgs()<<"\n";///////////
      insert_WS(v, i, sleep, sleep_trees, busy_n_hap_aft_witness, ongoing_msg);
      v_it = prefix.branch(i).pending_WSs.erase(v_it);
    }
    /* Reverse races */
    for (auto v : WSs[i]) {
      // for(Branch br:v) llvm::dbgs()<<"("<<threads[SPS.get_pid(br.spid)].cpid<<","<<br.index<<")";////////////
      // llvm::dbgs()<<"\n";///////////
      if (sequence_clears_sleep(v, sleep, sleep_trees, busy_n_hap_aft_witness))
	insert_WS(v, i, sleep, sleep_trees, busy_n_hap_aft_witness, ongoing_msg);
    }
    /* Add events in the witness events */
    update_witness_sets(index, prefix[i].end_of_msg(), handler,
			prefix[i].clock, sleep_trees, busy_n_hap_aft_witness);
    if(handler != -1){
      if(index == 1){
        ongoing_msg[handler] = threads[ipid].spid;
	handler_busy[handler] = true;
      } else if(prefix[i].end_of_msg()){
	ongoing_msg[handler] = 0;
	handler_busy[handler] = false;
      }
    }
    obs_sleep_wake(sleep, sleep_trees, prefix[i], multiple_handlers);
  }

  for (unsigned i = 0; i < prefix.len(); ++i) prefix[i].races.clear();
  lock_fail_races.clear();
}

void EventTraceBuilder::insert_WS(std::vector<Branch> &v, unsigned i,
				  struct obs_sleep sleep,
				  sleep_trees_t sleep_trees,
				  std::vector<std::vector<bool>> 
				  busy_n_hap_aft_witness,
				  std::vector<IPid> ongoing_msg){
  WakeupTreeRef<Branch> node = prefix.parent_at(i);
  bool leftmost_branch = true;
  VClock<IPid> second_br_clock = v.back().clock;
  std::vector<bool> handler_busy(threads.size(), false);
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
      std::vector<VClock<IPid>> clk_fst_of_msgs;
      std::vector<unsigned> u;
      bool branch_found = false;
      unsigned j = 0;
      IPid child_handler =
	threads[SPS.get_pid(child_it.branch().spid)].handler_id;
      unsigned last_seen_msg_event = 0;
      bool partial_msg = true;
      for(unsigned k = v.size()-1; k > j; --k){
	if(v[k].spid == child_it.branch().spid && last_seen_msg_event == 0){
	  last_seen_msg_event = k;
	  if(v[k].is_ret_stmt()) partial_msg = false;
	  break;
	}
      }
      VClock<IPid> clk_lst_msg_event = v[last_seen_msg_event].clock;
      bool multiple_handlers = false;
      IPid last_handler = -1;
      for (auto vei = v.begin(); skip == NO && vei != v.end(); ++vei, ++j) {
        const Branch &ve = *vei;
	if(!multiple_handlers && threads[SPS.get_pid(ve.spid)].handler_id != -1){
	  if(last_handler != -1 && threads[SPS.get_pid(ve.spid)].handler_id != last_handler)
	    multiple_handlers = true;
	  last_handler = threads[SPS.get_pid(ve.spid)].handler_id;
	}
        if (child_it.branch() == ve) {
	  branch_found = true;

          if (v.size() == 1) {
            /* v is about to run out, which means that we had already
             * scheduled an execution that was startable with v.
             * From this point, the recursive insertion is a no-op, so
             * exit early.
             */
            return;
          }

	  /* After finding first event of the message match the whole message */
	  /* if there is messages from the same handler before(clk_fst_of_msgs) */ 
	  /* and the message has more than one event */
	  if(threads[SPS.get_pid(ve.spid)].handler_id != -1 &&
	     ve.index == 1){
	    if(!clk_fst_of_msgs.empty()){
	      if(!v[j].is_ret_stmt()){
		if(partial_msg || !leftmost_branch){
		  auto res = child_it.branch().pending_WSs.insert(std::move(v));
		  // llvm::dbgs()<<child_it.branch().spid<<","<<child_it.branch().index<<"Parkq\n";//////////////
		  if(res.second) no_of_pending_WSs++;
		  return;
		}
		else if(conflict_with_rest_of_msg(j, child_it.branch(), v, clk_fst_of_msgs,
						  last_seen_msg_event, partial_msg) ||
			(multiple_handlers && !reordering_possible())){
		  skip = NEXT;
		  leftmost_branch = false;
		  break;
		}
	      }
	    }
	  }
          /* We will recurse into this node. To do that we first need to
           * drop all events in child_it.branch() from v.
           */
	  delete_matching_events(v, child_it.branch().size, vei);
	  if(!clk_fst_of_msgs.empty() && child_handler != -1 &&
	     child_it.branch().index == 1){
	    if(partial_msg){
	      /* delete the messages in the same handler before the current message */
	      /* and the events that are happening after them */
	      for(auto wei = v.begin(); wei != v.end(); wei++){
		for(VClock<IPid> clk : clk_fst_of_msgs){
		  if(clk.leq(wei->clock)){
		    wei = v.erase(wei);
		    wei--;
		    break;
		  }
		}
	      }
	    } else{
	      std::vector<Branch> msg;
	      for(unsigned k : u) msg.push_back(v[k]);
	      for(unsigned k = j; k < v.size(); k++){
		if(clk_lst_msg_event.geq(v[k].clock)){
		  u.push_back(k);
		  msg.push_back(v[k]);
		}
	      }
	      for(auto k = u.rbegin(); k != u.rend(); ){
		v.erase(v.begin()+(*k));
		k++;
		u.pop_back();
	      }
	      v.insert(v.begin(), msg.begin(), msg.end());
	    }
	  }
	  if(v.size() == 0) return; // after deleting multiple events, 
          break;
        } else if (child_handler != -1 && child_it.branch().index == 1){
	  if(threads[SPS.get_pid(ve.spid)].handler_id == child_handler){
	    /* This branch is incompatible, try the next */
	    if(!partial_msg){
	      if(ve.clock.lt(clk_lst_msg_event)){
	    	leftmost_branch = false;
	    	skip = NEXT;
	    	break;
	      }
	    } else if(leftmost_branch){
	      if(ve.index == 1){
	        clk_fst_of_msgs.push_back(v[j].clock);
	      }
	      IPid child_pid = SPS.get_pid(child_it.branch().spid);
	      /* Check if all the events of the message in WS is non-conflicting */
	      for(unsigned ei : threads[child_pid].event_indices){
		if(do_events_conflict(ve.spid, ve.sym,
				      child_it.branch().spid, prefix[ei].sym)){
		  //put the message in the sleep trees
		  std::list<Branch> explored_trail;
		  for(auto eit = threads[SPS.get_pid(child_it.branch().spid)].
			event_indices.begin();
		      eit != threads[SPS.get_pid(child_it.branch().spid)].
			event_indices.end();){
		    if(prefix.branch(*eit).access_global())
		      explored_trail.push_back(branch_with_symbolic_data(*eit));
		    eit += prefix.branch(*eit).size;
		  }
		  leftmost_branch = false;
		  skip = NEXT;
		  break;
		}
	      }
	    } else{
	      auto res = child_it.branch().pending_WSs.insert(std::move(v));
	      // llvm::dbgs()<<child_it.branch().spid<<","<<child_it.branch().index<<" Park\n";//////////////
	      if(res.second) no_of_pending_WSs++;
	      return;
	    }
	  } else{
	    unsigned last_index = threads[SPS.get_pid(child_it.branch().spid)].
	                          event_indices.size()-1;
	    unsigned last_ev =
	      find_process_event(SPS.get_pid(child_it.branch().spid),
				 last_index);
	    if(vei->clock.lt(prefix[last_ev].clock)) u.push_back(j);
	    if(do_events_conflict(ve.spid, ve.sym,
				  child_it.branch().spid, child_sym)){
	      leftmost_branch = false;
	      skip = NEXT;
	      break;
	    }
	    for(VClock<IPid> clk : clk_fst_of_msgs){
	      if(clk.lt(ve.clock)){
		IPid child_pid = SPS.get_pid(child_it.branch().spid);
	        for(unsigned ei : threads[child_pid].event_indices){
		  if(do_events_conflict(ve.spid, ve.sym,
				        child_it.branch().spid, prefix[ei].sym)){
		    leftmost_branch = false;
		    skip = NEXT;
		    break;
		  }
		}
		break;
	      }
	    }
	  }
	} else if (do_events_conflict(ve.spid, ve.sym,
				      child_it.branch().spid,
				      child_sym)) {
          /* This branch is incompatible, try the next */
	  leftmost_branch = false;
          skip = NEXT;
        }
      }

      if (skip == NEXT) {
	//Update sleep trees and sleepset
	if (child_handler != -1 && child_it.branch().index == 1){
	  std::list<Branch> explored_trail;
	  for(auto eit = threads[SPS.get_pid(child_it.branch().spid)].
		event_indices.begin();
	      eit != threads[SPS.get_pid(child_it.branch().spid)].
		event_indices.end();){
	    if(prefix.branch(*eit).access_global())
	      explored_trail.
		push_back(branch_with_symbolic_data(*eit));
	    eit += prefix.branch(*eit).size;
	  }
	  sleep_trees.push_back({child_it.branch().spid, 0,
				 std::vector<VClock<IPid>>(),
				 std::set<std::list<Branch>>
				 {std::move(explored_trail)},
	                         handler_busy});
	} else
	  sleep.sleep.push_back({child_it.branch().spid, &child_sym, nullptr});
	skip = NO; continue;
      }

      /* The child is compatible with v, recurse into it. */
      if(leftmost_branch && end_of_ws == i) return;
      if(!branch_found) return;
      i++;
      if(child_handler != -1 && child_it.branch().index == 1){
      	for(auto &slp_tree : sleep_trees){
      	  if(child_handler == threads[SPS.get_pid(slp_tree.spid)].handler_id)
      	    slp_tree.witness_events.push_back(child_it.branch().clock);
      	}
      }
      update_witness_sets(child_it.branch().index,
      			  child_it.branch().is_ret_stmt(),
      			  child_handler, prefix[i].clock,
      			  sleep_trees, busy_n_hap_aft_witness);
      obs_sleep_wake(sleep, sleep_trees, child_it.branch().spid,
      		     child_it.branch().index, child_it.branch().clock,
      		     child_it.branch().sym, multiple_handlers);
      node = child_it.node();
      if(threads[SPS.get_pid(child_it.branch().spid)].handler_id != -1){
	if(ongoing_msg[threads[SPS.get_pid(child_it.branch().spid)].handler_id] != 0){
	  if(child_it.branch().is_ret_stmt())
	    ongoing_msg[threads[SPS.get_pid(child_it.branch().spid)].handler_id] = 0;
	} else if(child_it.branch().index == 1)
	  ongoing_msg[threads[SPS.get_pid(child_it.branch().spid)].handler_id] =
	    child_it.branch().spid;
      }
      skip = RECURSE;
      break;

      assert(false && "UNREACHABLE");
      abort();
    }
    if (skip == RECURSE) continue;

    /* No existing child was compatible with v. Insert v as a new sequence. */
    std::map<IPid, std::vector<unsigned>> clear_set =
      mark_sleepset_clearing_events(v, sleep, sleep_trees);
    if(!remove_partial_msgs(v ,second_br_clock, clear_set, ongoing_msg)){
      //llvm::dbgs()<<"PROBLEM------\n";///////////////
      return;
    }

    if (!sequence_clears_sleep(v, sleep, sleep_trees, busy_n_hap_aft_witness)){
      // llvm::dbgs()<<"Redundant\n";/////////////////
      return;
    }
#ifndef NDEBUG
    bool problem = false;
    for (Branch &ve : v) {
      if(threads[SPS.get_pid(ve.spid)].handler_id != -1){
	if(ongoing_msg[threads[SPS.get_pid(ve.spid)].handler_id] != 0){
	  if(ve.is_ret_stmt())
	    ongoing_msg[threads[SPS.get_pid(ve.spid)].handler_id] = 0;
	} else if(ve.index == 1)
	  ongoing_msg[threads[SPS.get_pid(ve.spid)].handler_id] = ve.spid;
      }
      if(ongoing_msg[threads[SPS.get_pid(ve.spid)].handler_id] != 0 &&
	 ongoing_msg[threads[SPS.get_pid(ve.spid)].handler_id] != ve.spid){
	problem = true;
	break;
      }
    }
#endif
    for (Branch &ve : v) {
      if (conf.dpor_algorithm == Configuration::OBSERVERS)
        clear_observed(ve.sym);
      for (SymEv &e : ve.sym) e.purge_data();
      node = node.put_child(std::move(ve));
    }
#ifndef NDEBUG
    if(problem){
      Branch marker(0,1);
      node = node.put_child(marker);
      debug_print();
      exit(-6);
    }
#endif
    branches++;
    return;
  }
}



void EventTraceBuilder::
  delete_matching_events(std::vector<Branch> &v, unsigned child_size,
			 std::vector<Branch>::iterator vei){
  Branch ve = *vei;
  if (ve.size < child_size) {
    /* child_it.branch() contains more events than just ve.
     * We need to scan v to find all of them.
     */
    int missing = child_size - ve.size;
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
  } else if (ve.size > child_size) {
    /* ve is larger than child_it.branch(). Delete the common prefix from ve. */
    vei->size -= child_size;
    vei->sym.clear();
    vei->alt = 0;
  } else {
    /* Drop ve from v. */
    v.erase(vei);
  }
}

bool EventTraceBuilder::
reordering_possible() const{
  // TODO: saturation method
  // llvm::dbgs()<<"Incomplete WI check\n";
  return false;
}

bool EventTraceBuilder::
conflict_with_rest_of_msg(unsigned j, const Branch &child,
			  const std::vector<Branch> &v,
			  const std::vector<VClock<IPid>> &first_of_msgs,
			  unsigned &last_seen_msg_event,
			  bool &partial_msg) const{
  /* After finding first event of the message match the whole message */
  /* if there is messages from the same handler before(first_of_msgs) */
  /* and the message has more than one event */

  /* check if events from the message occurring in WS are conflicting */
  if(last_seen_msg_event > 0){
    for(VClock<IPid> clk : first_of_msgs){
      if(clk.lt(v[last_seen_msg_event].clock)){
	return true;
      }
    }
  }
  /* events are same as the current execution for partial non-branching message */
  /* check conflict for the rest of the message not in WS */
  // TODO: Branching case 
  if(partial_msg){
    unsigned last_index = v[last_seen_msg_event].index +
      v[last_seen_msg_event].size - 2;
    for(unsigned k = v.size()-1; k > j; --k){
      if(v[k].spid != child.spid){
	for(VClock<IPid> clk : first_of_msgs){
	  if(clk.leq(v[k].clock)){
	    std::vector<unsigned> event_indices =
	      threads[SPS.get_pid(child.spid)].event_indices;
	    for(unsigned ei = last_index+1; ei < event_indices.size(); ei++){
	      if(do_events_conflict(v[k].spid, v[k].sym,
				    child.spid, prefix[event_indices[ei]].sym)){
		return true;
	      }
	    }
	  }
	}
      }
    }
  }
  return false;
}

bool EventTraceBuilder::wakeup_sequence(const Race &race, unsigned &br_point,
					std::vector<bool> &in_notdep,
					Branch &second_br) const{
  int i = race.first_event;
  int j = race.kind != Race::MSG_REV? race.second_event : race.snd_conflict;
  IPid fpid = prefix[i].iid.get_pid();
  IPid spid = prefix[j].iid.get_pid();
  Event second({-1,0});
  // std::vector<unsigned>::const_iterator exclude{};
  // std::vector<unsigned>::const_iterator exclude_end = exclude;
  second_br = Branch(0,0);
  recompute_second(race,second_br,second);

  // if (race.kind == Race::SEQUENCE) {
  //   exclude = race.exclude.begin();
  //   exclude_end = race.exclude.end();
  //   if (conf.debug_print_on_reset)
  //     llvm::dbgs() << "SEQUENCE race with " << exclude_end - exclude << " exclusions\n";
  // }

  /* v is the subsequence of events in prefix come after prefix[i],
   * but do not "happen after" (i.e. their vector clocks are not strictly
   * greater than prefix[i].clock), followed by the second event.
   *
   * It is the sequence we want to insert into the wakeup tree.
   */
  std::vector<Branch> v;
  std::vector<const Event*> observers;
  std::vector<Branch> notobs;
  //std::vector<bool> in_notdep(prefix.len());
  std::vector<unsigned> fst_partial_msgs;
  /* w is sequence of partial messages and events */

  /* notdep and notobs computation */
  {
    std::vector<std::pair<bool,unsigned>> handler_free(threads.size(), std::pair<bool,unsigned>(true,0));
    br_point = i;

    /* in_notdep[k] is true if prefix[k] does not "happen after" prefix[i]
     * (their vector clocks are not strictly greater than prefix[i].clock).
     */
    for (unsigned k = 0; k < prefix.len(); ++k){
      IPid ipid = prefix[k].iid.get_pid();
      IPid handler = threads[ipid].handler_id;
      in_notdep[k] = true;
      if(threads[ipid].handler_id != -1 &&
	 !handler_free[threads[ipid].handler_id].first &&
	 !prefix[k].clock.lt(prefix[j].clock)){
	in_notdep[k] = false;
	continue;
      }
      if(ipid != fpid && handler != -1 &&
	 prefix[k].iid.get_index() == 1 && prefix[k].clock.lt(prefix[j].clock)){
	bool backtrack = false;
	for(auto ind : fst_partial_msgs)
	  if(ind < k && in_notdep[ind] && threads[prefix[ind].iid.get_pid()].handler_id == handler){
	    in_notdep[ind] = false;
	    k = ind;
	    backtrack = true;
	    break;
	  }
	if(backtrack){
	  if(br_point > k){
	    br_point = k;
	    for(IPid handler = 0; handler < threads.size(); handler+=2)
	      if(!handler_free[handler].first && handler_free[handler].second >= br_point)
		handler_free[handler].first = true;
	  }
	  for(auto it = fst_partial_msgs.begin(); it != fst_partial_msgs.end();)
	    if(*it > k){
	      it = fst_partial_msgs.erase(it);
	    } else it++;
	  continue;
	}
      }
      if(race.kind == Race::MSG_REV){
	if(ipid == fpid){
	  in_notdep[k] = false;
	  continue;
	}
	if(ipid == spid && k < race.snd_conflict){
	  //events before second conflict event in second message should be in notdep
	  in_notdep[k] = true;
	  continue;
	}
	if(k == race.snd_conflict){// second conflict of the race does not go in the notdep
	  in_notdep[k] = false;
	  continue;
	}
	//The events after the first half of the second message should be in the notdep
	if(prefix[k].iid.get_index() > 1){
	  unsigned last = find_process_event(ipid, prefix[k].iid.get_index()-1);
	  in_notdep[k] = in_notdep[last];
	} else in_notdep[k] = true;
	for (unsigned h : prefix[k].happens_after){
	  if(in_notdep[h] == false){
	    in_notdep[k] = false;
	    break;
	  }
	}
	if(in_notdep[k] == true){
	  for (auto race : prefix[k].races){
	    unsigned h = race.kind == Race::MSG_REV?
	      threads[prefix[race.first_event].iid.get_pid()].
	      event_indices.back() : race.first_event; 
	    if(in_notdep[h] == false){
	      in_notdep[k] = false;
	      break;
	    }
	  }
	}
	if(in_notdep[k] == true){//can be removed
	  for (unsigned h : prefix[k].eom_before){
	    if(in_notdep[h] == false){
	      in_notdep[k] = false;
	      break;
	    }
	  }
	}
      }
      else if(!prefix[i].clock.leq(prefix[k].clock)){
	if(prefix[k].iid.get_index() > 1){
	  unsigned last = find_process_event(ipid, prefix[k].iid.get_index()-1);
	  in_notdep[k] = in_notdep[last];
	} else in_notdep[k] = true;
	if(in_notdep[k]){
	  for (unsigned h : prefix[k].happens_after){
	    if(in_notdep[h] == false){
	      in_notdep[k] = false;
	      break;
	    }
	  }
	}
	if(in_notdep[k]){
	  for (auto race : prefix[k].races){
	    unsigned h = race.kind == Race::MSG_REV?
	      threads[prefix[race.first_event].iid.get_pid()].
	      event_indices.back() : race.first_event;
	    if(in_notdep[h] == false){
	      in_notdep[k] = false;
	      break;
	    }
	  }
	}
	if(in_notdep[k]){//can be removed
	  for (unsigned h : prefix[k].eom_before){
	    if(in_notdep[h] == false){
	      in_notdep[k] = false;
	      break;
	    }
	  }
	}
      }
      else {
	in_notdep[k] = false;
      }
      if(ipid != spid && !in_notdep[k] && threads[ipid].handler_id != -1 &&
	 threads[ipid].handler_id == threads[spid].handler_id &&
	 in_notdep[threads[ipid].event_indices.front()]){
	k = threads[ipid].event_indices.front();
	in_notdep[k] = false;
	if(br_point > k){
	  br_point = k;
	  for(IPid handler = 0; handler < threads.size(); handler+=2)
	    if(!handler_free[handler].first && handler_free[handler].second >= br_point)
	      handler_free[handler].first = true;
	}
	for(auto it = fst_partial_msgs.begin(); it != fst_partial_msgs.end();){
	  if(*it > k){
	    it = fst_partial_msgs.erase(it);
	  } else it++;
	}
	continue;
	
      }
      if(k >= br_point && !in_notdep[k] && threads[ipid].handler_id != -1 &&
	 handler_free[threads[ipid].handler_id].first &&
	 threads[ipid].event_indices.front() < br_point){
	handler_free[threads[ipid].handler_id].first = false;
	handler_free[threads[ipid].handler_id].second = threads[ipid].event_indices.front();
      }
      if(threads[ipid].handler_id != -1 && !in_notdep[k] &&
	 in_notdep[threads[ipid].event_indices.front()])
        fst_partial_msgs.push_back(threads[ipid].event_indices.front());
    }
    for(unsigned k = 0; k < prefix.len(); ++k){
      if(prefix[k].iid.get_pid() == spid && !in_notdep[k] && k < j) return false;
      //unfiltered_notdep.push_back(in_notdep[k]);
    }
  }
#ifndef NDEBUG
  for(unsigned k = 0; k < prefix.len(); ++k){
    if(in_notdep[k]){
      if(prefix[k].iid.get_index() > 1){
	unsigned last = find_process_event(prefix[k].iid.get_pid(), prefix[k].iid.get_index()-1);
	assert(in_notdep[last]);
      }
      for (unsigned h : prefix[k].happens_after)
	assert(in_notdep[h]);
      for (auto race : prefix[k].races){
	if(prefix[k].iid.get_pid() != spid ||
	   prefix[race.first_event].iid.get_pid() != fpid){
	  unsigned h = race.kind == Race::MSG_REV?
	    threads[prefix[race.first_event].iid.get_pid()].
	    event_indices.back() : race.first_event;
	  assert(in_notdep[h]);
	}
      }
      for (unsigned h : prefix[k].eom_before)
	assert(in_notdep[h]);
    }
  }
#endif
  if (race.kind == Race::NONBLOCK) {
    recompute_cmpxhg_success(second_br.sym, v, i);
  }
  return true;
}

bool EventTraceBuilder::
remove_partial_msgs(std::vector<Branch> &v, const VClock<IPid> &second_br_clock,
		    std::map<IPid, std::vector<unsigned>> clear_set,
		    std::vector<IPid> &ongoing_msg) const{
  //llvm::dbgs()<<"Hello1\n";/////////////
  unsigned old_size = v.size();
  /* partial_msg[k] = true iff k is partial in v */ 
  bool partial_msg[SPS.num_of_threads()];
  int first_of_msgs[threads.size()];
  for(IPid k = 0; k < threads.size(); k+=2){
    first_of_msgs[k] = -1;
    IPid handler = threads[SPS.get_pid(k)].handler_id;
    partial_msg[k] = false;
  }
  std::map<IPid, IPid> last_msg;
  for(unsigned k = 0; k < v.size(); k++){//collect partial msgs and first_of_msgs
    if(!partial_msg[v[k].spid] &&
       threads[SPS.get_pid(v[k].spid)].handler_id != -1){
      if(first_of_msgs[v[k].spid] == -1) first_of_msgs[v[k].spid] = k;
      partial_msg[v[k].spid] = true;
    }
    if(v[k].is_ret_stmt() && threads[SPS.get_pid(v[k].spid)].handler_id != -1){
      partial_msg[v[k].spid] = false;
      ongoing_msg[threads[SPS.get_pid(v[k].spid)].handler_id] = 0;
    }
  }
  for(IPid k = 0; k < threads.size(); k=k+2)
    if(ongoing_msg[k] != 0) last_msg[k] = ongoing_msg[k];
  
  for(auto evts = clear_set.begin(); evts != clear_set.end();){
    //No partial msg happening before clear set
    bool flag = false;
    for(unsigned ei : evts->second){
      for(int k = 0; k < int(threads.size()); k+=2){
      	if(partial_msg[k] && first_of_msgs[k] != -1 &&
	   v[first_of_msgs[k]].index==1 &&
      	   v[first_of_msgs[k]].clock.lt(v[ei].clock))
      	  flag = true;
      }
      if(!flag) break; 
    }
    if(!flag){
      evts = clear_set.erase(evts);
    } else evts++;
  }
  
  /* Last message in the handler is one happening before an event in the clear_set */
  std::map<IPid, unsigned> guess;
  for(auto evts : clear_set) guess[evts.first] = 0;
  bool next = false;
  for(auto g = guess.begin(); g != guess.end(); g++){// determine the last msg in a handler
    //if(!next){
      for(int k = 0; k < int(threads.size()); k+=2){
  	if(partial_msg[k] &&
	   v[first_of_msgs[k]].clock.leq(v[clear_set[g->first][g->second]].clock)){
  	  if(last_msg.find(threads[SPS.get_pid(k)].handler_id) ==
	     last_msg.end()){
  	    last_msg[threads[SPS.get_pid(k)].handler_id] = k;
	  }
  	  else if(last_msg[threads[SPS.get_pid(k)].handler_id] != k){
  	    //next = true;
  	    //break;
  	    return false;
  	  }
  	}
      }
      //}
      //if(next){
      // if(g->second+1 == clear_set[g->first].size()){
      // 	if(g == guess.begin()) return false;
      // 	g--;
      // }
      // else{
      // 	next = false;
      // 	g->second++;
      // }
      //}
    // else g++;
  }
  /* Choosing last message for rest of the handler */
  for(unsigned k = 0; k < threads.size(); k+=2){
    if(partial_msg[k] && last_msg.find(threads[SPS.get_pid(k)].handler_id) == last_msg.end()){
	last_msg[threads[SPS.get_pid(k)].handler_id] = k;
    }
  }

  std::vector<VClock<IPid>> clk_first_of_msgs(threads.size(), VClock<IPid>());
  bool reversible_race = true;
  for(unsigned k = 0; k<threads.size(); k+=2){
    if(first_of_msgs[k] != -1) clk_first_of_msgs[k] = v[first_of_msgs[k]].clock;
  }
  for(unsigned k = 0; k < threads.size(); k+=2){
    if(first_of_msgs[k] != -1 && partial_msg[k] &&
       last_msg.find(threads[SPS.get_pid(k)].handler_id) != last_msg.end() &&
       last_msg[threads[SPS.get_pid(k)].handler_id] != k){
      for(auto v_it = v.begin(); v_it != v.end();){
  	if(clk_first_of_msgs[k].leq(v_it->clock)){
	  if(v_it->clock.leq(second_br_clock)){
	    reversible_race = false;
	    break;
	  }
	  v_it = v.erase(v_it);
	}
  	else v_it++;
      }
      if(!reversible_race) break;
    }
  }
  if(!reversible_race){
    v.clear();
    return true;
  }
  bool linearized = true;
  std::vector<unsigned> curr_msg(threads.size(),0);
  for(unsigned k = 0; k < v.size(); k++){//collect partial msgs and first_of_msgs
    if(threads[SPS.get_pid(v[k].spid)].handler_id != -1){
      if(curr_msg[threads[SPS.get_pid(v[k].spid)].handler_id] != 0 &&
	 curr_msg[threads[SPS.get_pid(v[k].spid)].handler_id] != v[k].spid){
	linearized = false;
  	break;
      }
      curr_msg[threads[SPS.get_pid(v[k].spid)].handler_id] = v[k].spid;
    }
    if(v[k].is_ret_stmt()){
      curr_msg[threads[SPS.get_pid(v[k].spid)].handler_id] = 0;
    }
  }
  if(!linearized){
    if(old_size <= v.size()) return false;
    remove_partial_msgs(v, second_br_clock, clear_set, ongoing_msg);
  }
  return true;
}

std::vector<EventTraceBuilder::Branch> EventTraceBuilder::
linearize_sequence(unsigned br_point, Branch second_br,
		   const Race &race, std::vector<bool> &in_v) const{
  std::vector<std::set<unsigned>> trace(prefix.len());
  std::vector<Branch> linearized_ws;
  std::vector<VClock<IPid>> clock_WS(prefix.len());
  unsigned k = find_process_event(SPS.get_pid(second_br.spid),second_br.index);
  in_v[k] = true;
  recompute_vclock(in_v,clock_WS,trace,race);
  /* partial msgs goes after full msgs */
  std::vector<unsigned> last_msgs;
  for(int i = 2; i < threads.size(); i+=2){
    if(threads[i].handler_id != -1 &&
       !threads[i].event_indices.empty() &&
       threads[i].event_indices.front() > br_point &&
       in_v[threads[i].event_indices.front()] &&
       !in_v[threads[i].event_indices.back()]){
      IPid handler = threads[i].handler_id;
      for(int j = 2; j < threads.size(); j = j+2){
	if(i != j && threads[j].handler_id == threads[i].handler_id &&
	   !threads[j].event_indices.empty() &&
	   in_v[threads[j].event_indices.back()]){
	  trace[threads[i].event_indices.front()].
	    insert(threads[j].event_indices.back());
	}
      }
    }
  }
  in_v[k] = false;
  /* Do topological sort on the wakeup_sequence */
  std::vector<bool> visited(prefix.len(),false), visiting(prefix.len(),false);
  std::vector<unsigned> sorted_seq;
  std::vector<unsigned> curr_msg(threads.size(), 0);
  for(unsigned i = br_point; i < prefix.len(); i++){
    if(in_v[i] && !visited[i]){
      if(visit_event(br_point,i,in_v,trace,
		     visiting,visited,sorted_seq,curr_msg) == false){
	llvm::dbgs()
	  << "Linearize WS failed: as cycle in the wakeup sequence.\n";
        exit(1);
      }
    }
  }

  for(auto s_it = sorted_seq.begin(); s_it != sorted_seq.end(); s_it++){
    if(!in_v[*s_it]){
      s_it = sorted_seq.erase(s_it);
      s_it--;
      continue;
    }
    for(auto it = trace[*s_it].begin(); it != trace[*s_it].end();it++){//This loop will be eventually deleted
      if(!in_v[*it] &&
	 threads[prefix[*it].iid.get_pid()].event_indices.back() != *it){
	in_v[*s_it] = false;
	s_it = sorted_seq.erase(s_it);
	s_it--;
	break;
      }
    }
  }

  for(unsigned i : sorted_seq){
    Branch br = branch_with_symbolic_data(i);
    br.clock = clock_WS[i];
    linearized_ws.push_back(br);
  }
  second_br.clock = clock_WS[k];
  linearized_ws.push_back(second_br);
  return linearized_ws;
}

bool EventTraceBuilder::
visit_event(unsigned br_point, unsigned i, std::vector<bool> &in_v,
	    std::vector<std::set<unsigned>> &trace,
	    std::vector<bool> &visiting, std::vector<bool> &visited,
	    std::vector<unsigned> &sorted_seq,
	    std::vector<unsigned> &curr_msg) const{
  if(visiting[i] == true) return false;
  visiting[i] = true;
  IPid handler = threads[prefix[i].iid.get_pid()].handler_id;
  if(handler != -1 && curr_msg[handler] != 0 &&
     curr_msg[handler] != prefix[i].iid.get_pid()){
    unsigned last_of_curr_msg = threads[curr_msg[handler]].event_indices.back();
    if(last_of_curr_msg >= br_point && !visited[last_of_curr_msg] &&
       !visit_event(br_point,last_of_curr_msg,in_v,trace,
		    visiting,visited,sorted_seq,curr_msg)){
      visiting[i] = false;
      return false;
    }
  }
  for(auto it = trace[i].begin(); it != trace[i].end();){
    if(*it >= br_point && in_v[*it] == false){
      visiting[i] = false;
      in_v[i] = false;
      return true;
    } else if(*it >= br_point && !visited[*it]){
      if(!visit_event(br_point,*it,in_v,trace,visiting,
		      visited,sorted_seq,curr_msg)){
	visiting[i] = false;
	if((*it) <= i){
	  return false;
	}
	else{// Is it always a message
	  IPid pid = prefix[*it].iid.get_pid();
	  in_v[threads[pid].event_indices.front()] = false;
	  it = trace[i].erase(it);
	  //TODO: Remove the whole message
	}
      } else it++;
    } else it++;
  }
  visiting[i] = false;
  visited[i] = true;
  sorted_seq.push_back(i);
  if(handler != -1){
    if(prefix[i].iid.get_index() == 1)
      curr_msg[handler] = prefix[i].iid.get_pid();
    else if(threads[prefix[i].iid.get_pid()].event_indices.back() == i)
      curr_msg[handler] = 0;
  }
  return true;
}


void EventTraceBuilder::
recompute_vclock(const std::vector<bool> &in_v,
		 std::vector<VClock<IPid>> &clock_WS,
		 std::vector<std::set<unsigned>> &trace,
		 const Race &race) const{
  std::vector<unsigned> last_event(threads.size());
  std::vector<IPid> partial_msg(threads.size(),0);
  std::vector<bool> msg_starts_in_v(threads.size(),false);
  unsigned last_handler = -1;
  bool multiple_handlers=false;
  unsigned second = race.second_event;

  for(unsigned i = 0; i < prefix.len(); i++)
    if(in_v[i]) last_event[prefix[i].iid.get_pid()] = i;

  /* Recomputing clock for the WS*/
  for(unsigned i = 0; i < prefix.len();){
    if(!in_v[i] && i != second){
      clock_WS[i] = VClock<IPid>();
      i++;
      continue;
    }
    IPid pid = prefix[i].iid.get_pid();
    unsigned index = prefix[i].iid.get_index();
    IPid handler = threads[pid].handler_id;
    
    /* Detect multiple handlers */
    if(!multiple_handlers && handler != -1){
      if(last_handler != -1 && handler != last_handler)
	multiple_handlers = true;
      last_handler = handler;
    }
    
    if (index > 1) {
      unsigned last = find_process_event(pid,index-1);
      trace[i].insert(last);
      clock_WS[i] = clock_WS[last];
    } else {
      clock_WS[i] = VClock<IPid>();
    }
    clock_WS[i][pid] = index;
    for (unsigned ei : prefix[i].happens_after){
      assert(ei < i);
      trace[i].insert(ei);
      clock_WS[i] += clock_WS[ei];
    }
    /* Recompute races */ 
    for (auto r : prefix[i].races){//needs to be fixed
      assert(r.first_event < i);
      /* Consider the race we are currently reversing */
      if(prefix[r.first_event].iid.get_pid() == prefix[race.first_event].iid.get_pid() &&
	 r.first_event >= race.first_event){
	assert(r.first_event < i);
	if(r.kind == Race::MSG_REV){
	  /* If r is MSG_REV race, Consider the races between events e 
	   * before r.first_conflict and r.first_conflict */
	  for(Race rr : prefix[r.fst_conflict].races){
	    unsigned rr_fst = (rr.kind == Race::MSG_REV)? rr.fst_conflict : rr.first_event;
	    if(prefix[rr_fst].iid.get_pid() != prefix[i].iid.get_pid() &&
	       do_events_conflict(threads[prefix[rr_fst].iid.get_pid()].spid,
				  prefix[rr_fst].sym,
				  threads[prefix[r.snd_conflict].iid.get_pid()].spid,
				  prefix[r.snd_conflict].sym)){
	      unsigned rr_bef = (rr.kind == Race::MSG_REV)?
		threads[prefix[rr.first_event].iid.get_pid()].
		event_indices.back() : rr.first_event;
	      unsigned i_con = (rr.kind == Race::MSG_REV)? i : r.snd_conflict;
	      assert(rr_bef < i_con);
	      trace[i_con].insert(rr_bef);
	      clock_WS[i_con] += clock_WS[rr_bef];
	    }
	  }
	}
	/* Races between an event e before r.first_event and r.first_event*/
	for(Race rr : prefix[r.first_event].races){
	  unsigned rr_fst = (rr.kind == Race::MSG_REV)? rr.fst_conflict : rr.first_event;
	  assert(rr_fst < r.first_event);
	  if(prefix[rr_fst].iid.get_pid() != prefix[i].iid.get_pid() &&
	     do_events_conflict(threads[prefix[rr_fst].iid.get_pid()].spid,
				prefix[rr_fst].sym,
				threads[prefix[i].iid.get_pid()].spid,
				prefix[i].sym)){
	    bool msg_rev = r.kind != Race::MSG_REV &&
	      threads[prefix[i].iid.get_pid()].handler_id != -1 &&
	      threads[prefix[i].iid.get_pid()].handler_id ==
	      threads[prefix[rr.first_event].iid.get_pid()].handler_id;
	    unsigned rr_bef = msg_rev?
	      threads[prefix[rr.first_event].iid.get_pid()].
	      event_indices.back() : rr.first_event;
	    trace[i].insert(rr_bef);
	    clock_WS[i] += clock_WS[rr_bef];
	  }
	}
      } else{
	/* Races between other two messages */
	unsigned r_bef = (r.kind == Race::MSG_REV)?
	  threads[prefix[r.first_event].iid.get_pid()].
	  event_indices.back() : r.first_event;
	trace[i].insert(r_bef);
	clock_WS[i] += clock_WS[r_bef];
      }
    }
    bool backtrack = false;
    if(i == last_event[pid]){
      unsigned fev_i = threads[pid].event_indices.front();
      for (unsigned ej : prefix[fev_i].eom_before){
	unsigned fev_ej =
	  threads[prefix[ej].iid.get_pid()].event_indices.front();
	unsigned lev_ej =
	  threads[prefix[ej].iid.get_pid()].event_indices.back();
	assert(ej < i);
	assert(clock_WS[ej] != VClock<IPid>());
	assert(clock_WS[fev_ej] != VClock<IPid>());
	if(prefix[ej].iid.get_pid() != prefix[race.first_event].iid.get_pid() &&
	   clock_WS[fev_ej].lt(clock_WS[i]) &&
	   !clock_WS[ej].lt(clock_WS[fev_i])){
	  trace[fev_i].insert(ej);
	  clock_WS[fev_i] += clock_WS[ej];
	  backtrack = true;
	}
	/* Optimization that finds zigzag patterns of indirect dependency */    
	else if(multiple_handlers && !backtrack && !clock_WS[ej].lt(clock_WS[fev_i])){
	  bool ipid_after_j = false;
	  IPid j = prefix[ej].iid.get_pid();
	  std::vector<std::set<unsigned>> msgs_haft_j(threads.size());
	  std::vector<std::set<unsigned>> msgs_hbef_i(threads.size());
	  std::vector<bool> msg_aftj_n_befi(threads.size(),false);
	  for(IPid k = 2; k<threads.size(); k=k+2){
	    if(threads[k].handler_id == -1 || k==i || k==j ||
	       threads[k].event_indices.empty()) continue; 
	    unsigned fev_k = threads[k].event_indices.front();
	    unsigned lev_k = threads[k].event_indices.back();
	    bool after_j=false, before_i=false;
	    if(prefix[fev_k].clock.lt(prefix[i].clock)){
	      before_i=true;
	      msgs_hbef_i[threads[k].handler_id].insert(k);
	    }
	    if(prefix[fev_ej].clock.lt(prefix[lev_k].clock)){
	      after_j=true;
	      msgs_haft_j[threads[k].handler_id].insert(k);
	    }
	    if(after_j && before_i){
	      if(msg_aftj_n_befi[threads[k].handler_id]){
		ipid_after_j=true;
		break;
	      } else msg_aftj_n_befi[threads[k].handler_id]=true;
	    }
	  }
	  if(ipid_after_j){
	    trace[fev_i].insert(ej);
	    clock_WS[fev_i] += clock_WS[ej];
	    backtrack = true;
	  }
	}
      }
    }
    if(backtrack){
      for(unsigned j = i; j>=0; j--){
	if(threads[prefix[i].iid.get_pid()].event_indices.front() == j){
	  i = j+1;
	  break;
	}
	if(j==0) break;
      }
      continue;
    }
    i++;
  }
}
void EventTraceBuilder::
recompute_second(const Race &race, Branch &second_br, Event &second) const{
  unsigned i = race.first_event;
  unsigned j = race.second_event;
  const Event &first = prefix[i];
  if (race.is_fail_kind()) {
    second = reconstruct_blocked_event(race);
    /* XXX: Lock events don't have alternatives, right? */
    second_br = Branch(threads[second.iid.get_pid()].spid,
		       second.iid.get_index());
    second_br.sym = std::move(second.sym);
  } else if (race.kind == Race::NONDET) {
    second = first;
    second_br = branch_with_symbolic_data(i);
    second_br.alt = race.alternative;
  } else if (race.kind == Race::MSG_REV) {
    second = prefix[race.snd_conflict];
    second.sleep.clear();
    second.wakeup.clear();
    second_br = branch_with_symbolic_data(race.snd_conflict);
  }else {
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

void EventTraceBuilder::
  iid_map_step(std::vector<int> &iid_map, const Branch &event) const{
  if (iid_map.size() <= unsigned(event.spid)) iid_map.resize(event.spid+1, 1);
  iid_map[event.spid] += event.size;
}

void EventTraceBuilder::
  iid_map_step_rev(std::vector<int> &iid_map, const Branch &event) const{
  iid_map[event.spid] -= event.size;
}

VClock<int> EventTraceBuilder::reconstruct_blocked_clock(IID<IPid> event) const {
  VClock<IPid> ret;
  /* Compute the clock of the blocking process (event k in prefix is
   * something unrelated since this is a blocked event) */
  /* Find last event of p before this event */
  IPid p = event.get_pid();
  if (event.get_index() != 1) {
    int last = find_process_event(p, event.get_index()-1);
    ret = prefix[last].clock;
  }
  /* Recompute the clock of this mutex_lock_fail */
  ++ret[p];

  return ret;
}

EventTraceBuilder::Event EventTraceBuilder::
reconstruct_blocked_event(const Race &race) const {
  assert(race.is_fail_kind());
  Event ret(race.second_process);
  ret.clock = reconstruct_blocked_clock(race.second_process);

  if (race.kind == Race::LOCK_FAIL) {
    assert(std::any_of(prefix[race.first_event].sym.begin(),
                       prefix[race.first_event].sym.end(),
                       [](const SymEv &e){ return e.kind == SymEv::M_LOCK
                           || e.kind == SymEv::FULLMEM; }));
    ret.sym = prefix[race.first_event].sym;
  }
  // else {
  //   assert(race.kind == Race::SEQUENCE);
  //   ret.sym = {race.ev};
  // }
  return ret;
}

inline std::pair<bool,unsigned> EventTraceBuilder::
try_find_process_event(IPid pid, unsigned index) const{
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

inline unsigned EventTraceBuilder::find_process_event(IPid pid, unsigned index) const{
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
    throw std::
      logic_error("EventTraceBuilder::wakeup: Unknown type of memory access.");
  }

#ifndef NDEBUG
  if (conf.dpor_algorithm != Configuration::SOURCE) {
    VecSet<IPid> wakeup_set(wakeup);
    for (unsigned p = 0; p < threads.size(); ++p){
      if (!threads[p].sleeping) continue;
      assert(threads[p].sleep_sym);
      assert(bool(wakeup_set.count(p))
             == do_events_conflict(threads[pid].spid, ev, threads[p].spid, *threads[p].sleep_sym));
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
        if(0 < procs[i].store_index &&
	   stores[i][procs[i].store_index-1].store == next_pc){
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
