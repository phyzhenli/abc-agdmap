/**Source-File*************************************tab=2***************

  FileName    [agdmap.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Agdmap.]

  Synopsis    [External declarations.]

  Author      [Longfei Fan, Zhiyong Zhang, Chang Wu]

  Affiliation [Fudan University]

  Date        [August 1, 2023]

  Vision      [ 1.0 ]

***********************************************************************/

#include "agdmap.h"

namespace AgdMap
{

static int node_counter = 0;

  //===----------------------------------------------------------------------===//
  //                               Node class
  //===----------------------------------------------------------------------===//
  void Node::cutEnum(int lut_size, bool area_oriented)
  {
    if (cuts_.size() > 0 || (isChoice()))
    {
      return;
    }

    if (fanout_num_ == 0)
    {
      fanout_num_ = 1;
    }

    pCut min_dep_cutsize_ = nullptr;
    if (this->isPi())
    {
      pCut trivial_cut = std::make_shared<Cut>(this, 1.0, 1, Encode(id_));
      this->cuts_.push_back(trivial_cut);
      if (area_oriented == false)
      {
        min_dep_area_ = cuts_.front();
      }
      return;
    }

    if (fanin(0)->cutListNum() == 0 || fanin(1)->cutListNum() == 0)
    {
      return;
    }
    if (area_oriented)
    {
      utility::pruner<pCut, comp_pcut_area, sizer_pcut, pcut_area> pruner(lut_size);
      if (lut_size == 6)
      {
        pruner.reset_store_num_upper({0, 0, 1, 1, 1, 1, 3});
      }
      else if (lut_size == 4)
      {
        pruner.reset_store_num_upper({0, 0, 3, 4, 4});
      }
      else if (lut_size == 5)
      {
        pruner.reset_store_num_upper({0, 0, 3, 4, 4, 6});
      }
      else
      {
        assert(0);
      }

      for (auto it_l = fanin(0)->begin(); it_l != fanin(0)->end(); ++it_l)
        for (auto it_r = fanin(1)->begin(); it_r != fanin(1)->end(); ++it_r)
        {
          pCut cut = mergeCut(*it_l, *it_r, lut_size, area_oriented);
          if (cut && cut->cutsize() <= lut_size)
          {
            pruner.push(cut);
          }
        }
      pruner.collect(this->cuts_, area_oriented);
    }
    else
    {
      utility::pruner<pCut, comp_pcut_delay, sizer_pcut, pcut_area> pruner(lut_size);
      if (lut_size == 6)
      {
        pruner.reset_store_num_upper({0, 1, 1, 2, 2, 2, 3});
      }
      else if (lut_size == 4)
      {
        pruner.reset_store_num_upper({0, 1, 4, 6, 6});
      }
      else if (lut_size == 5)
      {
        pruner.reset_store_num_upper({0, 1, 1, 2, 4, 5});
      }
      else
      {
        assert(0);
      }
      for (auto it_l = fanin(0)->begin(); it_l != fanin(0)->end(); ++it_l)
        for (auto it_r = fanin(1)->begin(); it_r != fanin(1)->end(); ++it_r)
        {
          pCut cut = mergeCut(*it_l, *it_r, lut_size, area_oriented);
          if (cut && cut->cutsize() <= lut_size)
          {
            pruner.push(cut);
          }
        }
      pruner.collect(this->cuts_, area_oriented);
      min_dep_area_ = cuts_[0];
      for (int i = 1; i != cuts_.size(); ++i)
      {
        pCut cut = cuts_[i];
        if (min_dep_area_->depth() > cut->depth() || (min_dep_area_->depth() == cut->depth() && min_dep_area_->getArea() > cut->getArea()))
        {
          min_dep_area_ = cut;
        }
      }
    }

    this->cuts_.push_back(trivCutGen(area_oriented));
    this->setArea(minDepth()->getArea() / (Area)fanoutNum());
  }

  void Node::setAig(Node *fanin0, Node *fanin1, bool comple0, bool comple1)
  {
    fanins_[0] = fanin0;
    fanins_[1] = fanin1;
    comple_[0] = comple0;
    comple_[1] = comple1;
  }

  inline Depth Node::depth() { return min_dep_area_ == nullptr ? 0 : min_dep_area_->depth(); }

  pCut Node::mergeCut(const pCut &left, const pCut &right, int lut_size, bool area_oriented)
  {
    Sign sign = left->sign_ | right->sign_;
    if (countOnes64(sign) > lut_size)
      return nullptr;
    std::vector<Node *> inputs;
    if (utility::ordered_merge<Node *, pnode_id>(left->inputs(), right->inputs(), inputs, lut_size))
    {
      return nullptr;
    }
    Depth depth = 0;
    if (area_oriented == false)
      depth = right->depth() > left->depth() ? right->depth() : left->depth();
    Area sub_left = (left->getArea() - left->baseArea()) / (Area)(fanin(0)->fanoutNum());
    Area sub_right = (right->getArea() - right->baseArea()) / (Area)(fanin(1)->fanoutNum());
    Area area = sub_left + sub_right + 1.0;
    Function left_func = left->func();
    Function right_func = right->func();
    if (complement(0))
    {
      left_func = ~left_func;
    }
    if (complement(1))
    {
      right_func = ~right_func;
    }
    Function func = left_func & right_func;
    return std::make_shared<Cut>(inputs, area, depth, this, func, sign);
  }

  inline pCut Node::trivCutGen(bool area_oriented)
  {
    Area area = area_oriented ? minArea()->getArea() + 1.0 : minDepth()->getArea() + 1.0;
    Depth depth = area_oriented ? 0 : this->depth() + 1;
    return std::make_shared<Cut>(this, area, depth, Encode(id_));
  }

  void Node::p(std::string name = "node")
  {
    std::cout << "(" << name << ") " << this->getId() << "\t| ";
    std::cout << "fanins: ";
    if (isPi() == false)
    {
      std::cout << fanin(0)->getId() << "(" << comple_[0] << ") ";
      std::cout << fanin(1)->getId() << "(" << comple_[1] << ") \t";
    }
    std::cout << std::endl;
  }

  NodeSol Node::lutSol(Solution *sol, bool if_div, bool flow, Level required)
  {
    if (cuts_.size() == 1)
    {
      assert(virtual_);
      assert(cuts_[0]->depth() <= required);
      NodeSol nSol(NodeSol::Lut, cuts_[0]->getArea());
      nSol.nodes.push_back(this);
      nSol.lut_sol = cuts_[0];
      return nSol;
    }

    pCut selected = nullptr;
    Area min = 0;
    for (int i = 0; i != cuts_.size() - 1; ++i) // skip the trivial cut
    {
      pCut &cut = cuts_[i];
      if (cut->depth() > required)
      {
        continue;
      }
      Area tmp = flow ? cut->localFlow() : cut->localArea(if_div);
      if (selected == nullptr || tmp < min || (!flow && tmp == min && cut->getArea() < selected->getArea()))
      {
        selected = cut;
        min = tmp;
      }
    }

    assert(selected);
    assert(min < SSINF);
    NodeSol nSol(NodeSol::Lut, min);
    nSol.nodes.push_back(this);
    nSol.lut_sol = selected;
    return nSol;
  }

  NodeSol Node::minAreaIncSol(Solution *sol, bool flow, Level required)
  {
    bool if_div = true;
    NodeSol lut = lutSol(sol, if_div, flow, required);
    return lut;
  }

  void Node::dereference()
  {
    if (isAnd() && --fanout_num_ == 0)
    {
      fanins_[0]->dereference();
      fanins_[1]->dereference();
      setChoice();
    }
  }

  NodeSol &NodeSol::operator+=(const NodeSol &nSol)
  {
    if (this == &nSol)
      return *this;
    this->area += nSol.area;
    for (size_t i = 0; i != nSol.nodes.size(); ++i)
    {
      this->nodes.push_back(nSol.nodes[i]);
    }
    return *this;
  }

  Level NodeSol::getLevel()
  {
    if (area == SSINF)
      return SSINF;
    if (ll != 0)
      return ll;
    assert(type > 0);
    Level delay = 0.4;
    Level max_in = 0;
    for (Node *node : nodes)
    {
      max_in = node->depth() > max_in ? node->depth() : max_in;
    }
    max_in += delay;
    ll = max_in;
    return max_in;
  }

  //===----------------------------------------------------------------------===//
  //                               Cut class
  //===----------------------------------------------------------------------===//
  std::string Cut::p(bool simple)
  {
    std::string cut = root_->name() + " " + std::to_string(cutsize()) + " # { ";
    std::vector<Node *>::iterator it;
    for (it = inputs_.begin(); it != --inputs_.end(); ++it)
    {
      cut += " ";
      cut += std::to_string((*it)->getId());
      cut += ",";
    }
    cut += " ";
    cut += std::to_string((*it)->getId());
    if (simple)
    {
      cut += " } ";
      return cut;
    }
    else
    {
      cut += " } # ";
    }
    cut += std::to_string(depth_);
    cut += " # ";
    cut += std::to_string(getArea());
    return cut;
  }

  Cut::Cut(const pGate &gate) { inputs_.insert(inputs_.end(), gate->inputs().begin(), gate->inputs().end()); }

  Area Cut::localArea(bool if_div)
  {
    Area area = 0;
    for (auto it = begin(); it != end(); ++it)
    {
      Node *node = *it;
      area += node->area();
    }
    if (if_div == false)
    {
      if (type_ == General)
        area += 1.0;
      else if (type_ == Cut7)
        area += 2.0;
      else if (type_ == Cut8)
        area += 4.0;
      else if (type_ == Cut9)
        area += 8.0;
    }
    else
    {
      area /= (Area)cutsize(); // pure LUT compare
    }
    return area;
  }

  Area Cut::localFlow()
  {
    Area flow = 0;
    for (Node *node : inputs_)
    {
      flow += node->flow();
    }
    return flow + 1.0;
  }

  bool Cut::operator==(const Cut &cut)
  {
    if (area_ != cut.getArea())
      return false;
    if (depth_ != cut.depth())
      return false;
    return inputs_ == cut.inputs_;
  }

  inline Area Cut::baseArea()
  {
    int cutsize = inputs_.size() > 6 ? inputs_.size() : 6;
    return pow(2.0, cutsize - 6);
  }

  float Cut::getDelay()
  {
    switch (type_)
    {
    case General:
      return 1.0;
      break;
    case Cut7:
      return 1.2;
      break;
    case Cut8:
      return 1.4;
      break;
    case Cut9:
      return 1.6;
      break;
    default:
      assert(0);
      break;
    }
    return 0;
  }

  //===----------------------------------------------------------------------===//
  //                               Solution class
  //===----------------------------------------------------------------------===//
  Solution::Solution(Mapper *mapper)
  {
    lut_ = rtl_f7_ = rtl_f8_ = rtl_f9_ = 0;
    logic_level_ = 0;
    this->mapper = mapper;
    lut_num_.resize(6);
    for (int i = 0; i < mapper->poNum(); ++i)
    {
      Node *fanin = mapper->getPo(i)->fanin(0);
      assert(fanin);
      if (fanin->isAnd())
      {
        add(fanin, nullptr);
        fanin->setArea(0.0);
        fanin->setFlow(0.0);
      }
    }
  }

  Level Solution::getLevel()
  {
    if (logic_level_ != 0)
      return logic_level_;
    Level sol_ll = 0;
    std::map<int, Level> node_lvl;
    for (auto it = mapper->begin(); it != mapper->end(); ++it) // traverse all the nodes form PI to PO
    {
      Node *node = *it;
      pCut cut = nullptr;
      if (isRoot(node))
      {
        cut = repCut(node);
        assert(cut);
        Level max_ll = 0;
        for (auto in_it = cut->begin(); in_it != cut->end(); ++in_it)
        {
          auto it = node_lvl.find((*in_it)->getId());
          Level ll = it == node_lvl.end() ? 0 : it->second; // eq end() means *in_it is a PI
          max_ll = ll > max_ll ? ll : max_ll;
        }
        node_lvl.insert(std::pair<int, Level>(node->getId(), max_ll + cut->getDelay()));
      }
    }
    for (size_t i = 0; i < mapper->poNum(); ++i)
    {
      if (mapper->getPo(i)->fanin(0) == nullptr)
        continue;
      int id = mapper->getPo(i)->fanin(0)->getId();
      sol_ll = node_lvl[id] > sol_ll ? node_lvl[id] : sol_ll;
    }
    logic_level_ = sol_ll;
    return sol_ll;
  }

  void Solution::add(Node *node, const pCut &rep)
  {
    sol_[node] = rep;
    if (rep == nullptr)
    {
      weight_[node]++;
    }
    else
    {
      size_t cutsize = rep->cutsize();
      Cut::cut_type type = rep->getType();
      switch (type)
      {
      case Cut::General:
        ++lut_;
        ++lut_num_[cutsize - 1];
        break;
      case Cut::Cut7:
        lut_ += 2;
        lut_num_[5] += 2;
        break;
      case Cut::Cut8:
        lut_ += 4;
        lut_num_[5] += 4;
        break;
      case Cut::Cut9:
        lut_ += 8;
        lut_num_[5] += 8;
        break;
      default:
        assert(0);
        break;
      }
    }
  }

  //===----------------------------------------------------------------------===//
  //                               Mapper class
  //===----------------------------------------------------------------------===//
  Mapper::~Mapper()
  {
    pNtk_ = nullptr;
    if (best_sol_ != nullptr)
    {
      delete best_sol_;
    }
    std::unordered_set<int> nodes;
    for (size_t i = 0; i < nodes_.size(); ++i)
    {
      if (nodes.count(nodes_[i]->getId()) == 0)
      {
        nodes.insert(nodes_[i]->getId());
        delete nodes_[i];
      }
    }

    for (size_t i = 0; i < Po_.size(); ++i)
    {
      delete Po_[i];
    }
    delete const_1_;
  }

  float getCutExactArea(const pCut &cut, std::map<Node *, float> &exact)
  {
    float area = 0;
    for (auto it = cut->begin(); it != cut->end(); ++it)
    {
      area += exact[*it];
    }
    return area;
  }

  void Mapper::init()
  {
    node_counter = Abc_NtkObjNum(pNtk_);
    std::map<Node *, AbcNode *> node2abc;
    std::map<AbcNode *, Node *> abc2node;
    int cuts_num = isAreaOriented() ? 8 : 12;
    for (int i = 0; i < pNtk_->vObjs->nSize; ++i)
    {
      AbcNode *abc_obj = Abc_NtkObj(pNtk_, i);
      if (abc_obj == nullptr)
        continue;
      assert(abc_obj->Id < node_counter);
      Node *node = nullptr;
      if (abc_obj->Type == 2)
      {
        node = new Node(Node::Pi, abc_obj->Id, Abc_ObjName(abc_obj), Abc_ObjFanoutNum(abc_obj), abc_obj->fPhase, cuts_num);
        Pi_.push_back(node);
        nodes_.push_back(node);
      }
      else if (abc_obj->Type == 3)
      {
        continue;
      }
      else if (abc_obj->Type == 7)
      {
        node = new Node(Node::And, abc_obj->Id, Abc_ObjName(abc_obj), Abc_ObjFanoutNum(abc_obj), abc_obj->fPhase, cuts_num);
        nodes_.push_back(node);
      }
      else
      {
        // const 1
        node = new Node(Node::Cns, abc_obj->Id, Abc_ObjName(abc_obj), Abc_ObjFanoutNum(abc_obj), abc_obj->fPhase, cuts_num);
        const_1_ = node;
      }
      abc2node[abc_obj] = node;
      node2abc[node] = abc_obj;
    }

    // collect the nodes
    for (Node *node : nodes_)
    {
      if (node->isPi())
        continue;
      AbcNode *abc_node = node2abc[node];
      AbcNode *fanin0 = Abc_ObjFanin0(abc_node);
      AbcNode *fanin1 = Abc_ObjFanin1(abc_node);
      node->setAig(abc2node[fanin0], abc2node[fanin1], abc_node->fCompl0, abc_node->fCompl1);
    }

    for (int i = 0; i < Abc_NtkPoNum(pNtk_); ++i)
    {
      AbcNode *po = Abc_NtkPo(pNtk_, i);
      Node *node = new Node(Node::Po, po->Id, Abc_ObjName(po), Abc_ObjFanoutNum(po), po->fPhase, 1);
      AbcNode *fanin0 = Abc_ObjFanin0(po);
      assert(abc2node.find(fanin0) != abc2node.end());
      node->setAig(abc2node[fanin0], nullptr, po->fCompl0, false);
      Po_.push_back(node);
    }
    // collect the choice nodes and fix the fanout error
    // this step is necessary in spite of using choice to map or not
    if (Abc_NtkGetChoiceNum(pNtk_) != 0)
    {
      // collect the choice nodes
      for (Node *node : nodes_)
      {
        if (node->isAnd() && node2abc[node]->pData != nullptr && node->fanoutNum() != 0)
        {
          Abc_Obj_t *choice = static_cast<Abc_Obj_t *>(node2abc[node]->pData);
          while (choice)
          {
            Node *coreponding_node = abc2node[choice];
            node->choice.push_back(coreponding_node);
            choice = static_cast<Abc_Obj_t *>(choice->pData);
          }
        }
      }

      // fix the bias of fanout number of nodes : deference the choice nodes in netlist
      for (Node *node : nodes_)
      {
        if (node->choice.size() != 0)
        {
          for (Node *ch_node : node->choice)
          {
            assert(ch_node->fanoutNum() == 0);
            ch_node->fanin(0)->dereference();
            ch_node->fanin(1)->dereference();
            ch_node->setChoice();
            ch_node->setFanoutNum(node->fanoutNum()); // fanout num of choice nodes(exclude chice root) shall be 0
          }
          std::vector<Node *>().swap(node->choice);
        }
      }
    } // end choice pre-process
  }

  int Mapper::map()
  {
    auto elapse_start = std::chrono::high_resolution_clock::now();
    auto cpu_start = clock();
    // initialize
    init();
    // end init

    // Simultaneous gate decompose and tech mapping
    if (getGateSize() > 0)
    {
      // generating the simple gates according to the given netlist and do not
      // considering choice node(casuse they don't connected in netlist)
      simpleGateGen(getGateSize());
      if (verbose())
      {
        std::cout << "+  Simple Gates + \n";
        for (int i = 2; i <= getGateSize(); ++i)
        {
          if (simple_gates_num_[i] != 0)
            std::cout << "   " << i << "\t|  " << simple_gates_num_[i] << "\n";
        }
        std::cout << "+---------------+\n";
      }

      nodes_with_virtual_.reserve(nodes_.size() * 2);

      for (auto it = begin(); it != end(); ++it)
      {
        Node *node = *it;
        if (node->isPi())
        {
          node->cutEnum(getLutSize(), isAreaOriented());
          nodes_with_virtual_.push_back(node);
        }
        else if (node->sGate() != nullptr)
        {
          node->sGate()->SimpleGateEnum(getLutSize(), isAreaOriented(), this->nodes_with_virtual_);
          this->nodes_with_virtual_.push_back(node);
        }
        else if (!isAreaOriented()) // choice nodes and internal nodes of simple gate
        {
          node->cutEnum(getLutSize(), false);
          this->nodes_with_virtual_.push_back(node);
        }
      }
      this->nodes_.swap(this->nodes_with_virtual_);
      std::vector<Node *>().swap(this->nodes_with_virtual_);
    }
    else
    {
      // cut enumeration
      for (Node *node : nodes_)
      {
        node->cutEnum(getLutSize(), isAreaOriented());
      }
    }

    // free the big diff_level_nodes vector
    {
      std::vector<std::vector<Node *>> temp_vec;
      temp_vec.swap(diff_level_nodes_);
    }
    auto elapse_enum_end = std::chrono::high_resolution_clock::now();

    // set the mapping target delay
    if (!isAreaOriented())
    {
      Level sol_ll = getIdealDepth();
      for (size_t i = 0; i < poNum(); ++i)
      {
        Node *node = getPo(i)->fanin(0);
        if (node->isAnd())
        {
          required_[node] = sol_ll;
        }
      }
    }

    // full delay-oriented cut selection
    if (!isAreaOriented())
    {
      Solution *delay_sol = new Solution(this);
      for (auto it = rbegin(); it != rend(); ++it)
      {
        Node *node = *it;
        if (delay_sol->isRoot(node) == false || delay_sol->repCut(node) != nullptr)
        {
          continue;
        }
        pCut sel = node->minDepth();
        // general lut selection
        delay_sol->add(node, sel);
        for (auto node_it = sel->begin(); node_it != sel->end(); ++node_it)
        {
          if ((*node_it)->isAnd())
          {
            delay_sol->add(*node_it, nullptr);
          }
        }
      } // end selection
      for (Node *node : nodes_)
      {
        if (node->isAnd())
        {
          node->setArea(node->minDepth()->getArea() / (Area)delay_sol->fanout(node));
        }
      }
      delete delay_sol;
    }

    // effective area pass
    Solution *area_sol = new Solution(this);
    cutSel(area_sol, isAreaOriented(), false);
    int itr_num = 8;
    itrSel(area_sol, itr_num, isAreaOriented(), false);

    // initialize the area flow of nodes
    updateFlow(area_sol);

    // area flow pass
    Solution *lut_sol = new Solution(this);
    cutSel(lut_sol, isAreaOriented(), true);
    itrSel(lut_sol, itr_num, isAreaOriented(), true);

    // compare
    if (lut_sol->getArea() < area_sol->getArea() || (lut_sol->getArea() == area_sol->getArea() && lut_sol->getLevel() < area_sol->getLevel()))
    {
      delete area_sol;
    }
    else
    {
      delete lut_sol;
      lut_sol = area_sol;
    }

    best_sol_ = lut_sol;

    auto elapse_sel_end = std::chrono::high_resolution_clock::now();

    auto elapse_end = std::chrono::high_resolution_clock::now();
    auto cpu_end = clock();
    pNtk_ = agdmapToAbcLogic();
    // dumpTempNetwork();
    // pNtk_ = Io_Read( "_temp_.v", IO_FILE_VERILOG, 1, 0);
    // if (pNtk_)
    //   system("rm ./_temp_.v");

    double total_cpu_time = (cpu_end - cpu_start) * 1.0 / CLOCKS_PER_SEC;
    double total_elapse_time = (std::chrono::duration<double, std::milli>(elapse_end - elapse_start)).count() / 1000.0; // ms->sec

    if (verbose())
    {
      int enumerate = (std::chrono::duration<double, std::milli>(elapse_enum_end - elapse_start)).count() / 1000.0 / total_elapse_time * 100.0;
      int select = (std::chrono::duration<double, std::milli>(elapse_sel_end - elapse_enum_end)).count() / 1000.0 / total_elapse_time * 100.0;
      std::string space = " ";
      std::string empty = "";
      std::string t2 = total_cpu_time > 0.005 ? (enumerate < 10 ? space : empty) + std::to_string(enumerate) : "--";
      std::string t3 = total_cpu_time > 0.005 ? (select < 10 ? space : empty) + std::to_string(select) : "--";
      std::cout << std::endl;
      std::cout << "        runtime report       \n";
      std::cout << "+--------------------------------+\n";
      std::cout << "|  Enum             \t" << t2 << " %     |\n";
      std::cout << "|  Sele             \t" << t3 << " %     |\n";
      std::cout << "|--------------------------------|\n";
      std::string cpu_time = std::to_string(total_cpu_time);
      std::string elapse_time = std::to_string(total_elapse_time);
      if (total_cpu_time >= 100000)
        cpu_time = std::string(cpu_time, 0, 6);
      else if (total_cpu_time >= 10000)
        cpu_time = std::to_string((int)total_cpu_time);
      else if (total_cpu_time >= 1000)
        cpu_time = std::string(" ") + std::to_string((int)total_cpu_time);
      else if (total_cpu_time >= 100)
        cpu_time = std::string("  ") + std::to_string((int)total_cpu_time);
      else
        cpu_time = std::string(cpu_time, 0, 5);
      if (total_elapse_time >= 100000)
        elapse_time = std::string(elapse_time, 0, 6);
      else if (total_elapse_time >= 10000)
        elapse_time = std::to_string((int)total_elapse_time);
      else if (total_elapse_time >= 1000)
        elapse_time = std::string(" ") + std::to_string((int)total_elapse_time);
      else if (total_elapse_time >= 100)
        elapse_time = std::string("  ") + std::to_string((int)total_elapse_time);
      else
        elapse_time = std::string(elapse_time, 0, 5);
      std::cout << "|  cpu  	   \t" << cpu_time << " sec|\n";
      std::cout << "|  elapse 	 \t" << elapse_time << " sec|\n";
      std::cout << "+--------------------------------+\n";
      printRel(best_sol_);
    }

    return 0;
  }

  void Mapper::cutSel(Solution *sol, bool area_oriented, bool flow)
  {
    auto required = required_;
    for (auto it = rbegin(); it != rend(); ++it)
    {
      Node *node = *it;
      if (sol->isRoot(node) == false || sol->repCut(node) != nullptr)
      {
        continue;
      }
      pCut sel = nullptr;
      Level req = area_oriented ? SSINF : required.find(node)->second;
      NodeSol nSol = node->minAreaIncSol(sol, flow, req);
      sel = nSol.lut_sol;
      // general lut selection
      sol->add(node, sel);
      for (auto node_it = sel->begin(); node_it != sel->end(); ++node_it)
      {
        if ((*node_it)->isPi())
        {
          continue;
        }
        else
        {
          sol->add(*node_it, nullptr);
          if (flow)
            (*node_it)->setFlow(0);
          else
            (*node_it)->setArea(0);
          if (area_oriented == false)
          {
            if (required.find(*node_it) == required.end() || required[*node_it] > req - 1)
            {
              assert((*node_it)->depth() <= req - 1);
              required[*node_it] = req - 1;
            }
          }
        }
      }
    } // end selection
  }

  void Mapper::updateFlow(Solution *sol)
  {
    for (auto it = begin(); it != end(); ++it)
    {
      Node *node = *it;
      int last_req = sol->isRoot(node) ? sol->repCut(node)->depth() : SSINF;
      if (node->isPi())
      {
        node->setFlow(0);
        continue;
      }
      if (node->isChoice())
      {
        continue;
      }
      Area min_flow = SSINF;
      int bound = 0;
      if (!isAreaOriented())
      {
        bound = std::max(node->cutListNum() - 1, 0);
      }
      else
      {
        bound = std::max(node->isVirtual() ? 1 : node->cutListNum() - 1, 0);
      }
      for (int i = 0; i != bound; ++i)
      {
        if (node->getCut(i)->depth() <= last_req)
        {
          Area temp = node->getCut(i)->localFlow();
          if (min_flow > temp)
          {
            min_flow = temp;
          }
        }
      }
      assert(min_flow < SSINF);
      Area fanout = (Area)sol->fanout(node);
      node->setFlow((min_flow) / fanout);
    }
  }

  void Mapper::printRel(Solution *sol)
  {
    int lut_total = sol->getArea();
    int bound = getLutSize();
    if (!isAreaOriented())
    {
      getIdealDepth();
    }
    std::cout << std::endl;
    std::cout << "        primitives report       " << std::endl;
    std::cout << "+-------------------------------+" << std::endl;
    for (int i = 1; i <= bound; ++i)
    {
      if (lut_total == 0)
        std::cout << "|  LUT" << i << "     " << 0 << "\t%   \t" << sol->lutNum(i) << "\t|\n";
      else
        std::cout << "|  LUT" << i << "     " << 100 * sol->lutNum(i) / lut_total << "\t%   \t" << sol->lutNum(i) << "\t|\n";
    }
    std::cout << "|                               |\n";
    std::cout << "|  LUT      "
              << "          \t" << lut_total << "\t|\n";
    std::cout << "|-------------------------------|\n";
    if (!isAreaOriented())
      std::cout << "|  Ideal Lvl"
                << "     \t" << ideal_depth_ << "\t|\n";
    std::cout << "|  Final Lvl"
              << "     \t" << sol->getLevel() << "\t|\n";
    std::cout << "+-------------------------------+" << std::endl;
    std::cout << std::endl;
  }

  void Mapper::itrSel(Solution *&initial_sol, int max_itr_num, bool area_oriented, bool flow)
  {
    int num = 1;
    while (max_itr_num != 0)
    {
      Solution *new_sol = new Solution(this);
      // updateArea
      if (flow)
        updateFlow(initial_sol);
      else
      {
        for (auto it = begin(); it != end(); ++it)
        {
          Node *node = *it;
          if (node->isAnd())
          {
            if (initial_sol->isRoot(node))
              node->setArea(initial_sol->repCut(node)->getArea() / (Area)initial_sol->fanout(node));
            else
              node->setArea(node->minDepth()->getArea() / (Area)initial_sol->fanout(node));
          }
        }
      }
      cutSel(new_sol, area_oriented, flow);
      ++num;
      float new_area = new_sol->getArea();
      float init_area = initial_sol->getArea();
      float ratio = (flow ? 0.998 : 0.995);
      if (new_area < init_area || (area_oriented == false && new_area == init_area && new_sol->getLevel() < initial_sol->getLevel()))
      {
        delete initial_sol;
        initial_sol = new_sol;
        if (new_area / init_area < ratio)
          --max_itr_num;
        else
          break;
      }
      else
      {
        delete new_sol;
        break;
      }
    } // end while
  }

  Depth Mapper::getIdealDepth()
  {
    if (ideal_depth_ != 0)
    {
      return ideal_depth_;
    }
    for (size_t i = 0; i < poNum(); ++i)
    {
      Node *node = getPo(i)->fanin(0);
      if (node->isAnd() && ideal_depth_ < node->depth())
      {
        ideal_depth_ = node->depth();
      }
    }
    return ideal_depth_;
  }

  void Mapper::simpleGateGen(int gate_size_upper)
  {
    std::set<Node *> sgate_roots;
    for (Node *po : Po_)
    {
      if (po->fanin(0)->isAnd())
      {
        sgate_roots.insert(po->fanin(0));
      }
    }
    for (auto it = rbegin(); it != rend(); ++it)
    {
      Node *node = *it;
      if (sgate_roots.find(node) != sgate_roots.end())
      {
        pGate gate = std::make_shared<SimpleGate>(node);
        gate->expand(gate_size_upper);
        auto vec = gate->inputs();
        for (auto n : vec)
        {
          if (n->isPi() == false)
            sgate_roots.insert(n);
        }
        node->setSgate(gate);
        simple_gates_num_[gate->size()]++;
      }
    }
  }

  // translate func to true valule(hex).
  std::string Mapper::expToTrueValue(const std::vector<Node *> &inputs, const std::string &exp)
  {
    utility::QMP<uint64_t> qmp;
    // printf("exp: %s\n", exp.c_str());
    for (int i = 0; i < inputs.size(); ++i)
    {
      //qmp.addVar(inputs[i]->name());
      qmp.addVar("n" + std::to_string(inputs[i]->getId()));
    }
    qmp.set_output("O5");
    uint64_t truth = qmp.getTruthValue(exp);
    int len = 1;
    if (inputs.size() > 2)
    {
      len = 1 << (inputs.size() - 2);
    }
    std::string buf = utility::int2Hex(truth, len);
    return buf;
  }

  // translate the result of agdmap to Abc logic(sop).
  Abc_Ntk_t *Mapper::agdmapToAbcLogic()
  {
    Abc_Obj_t *pNode;
    Abc_Obj_t *pNet;
    char *pWord = new char[1024];
    // start the network
    Abc_Ntk_t *pNtkNetlist = Abc_NtkAlloc(ABC_NTK_NETLIST, ABC_FUNC_SOP, 1);
    pNtkNetlist->pName = Extra_UtilStrsav(pNtk_->pName);
    pNtkNetlist->pSpec = Extra_UtilStrsav(pNtk_->pSpec);

    // create PI.
    for (Node *pi : Pi_)
    {
      strcpy(pWord, pi->name().c_str());
      pNode = Abc_NtkCreateObj(pNtkNetlist, ABC_OBJ_PI);
      Abc_ObjAssignName(pNode, pWord, NULL);
      pNet = Abc_NtkFindOrCreateNet(pNtkNetlist, pWord);
      Abc_ObjAddFanin(pNet, pNode);
    }
    std::set<Node *> bound;
    std::map<Node *, Function> funcs;
    for (Node *node : Po_)
    {
      // 1. create PO (abc node).
      strcpy(pWord, node->name().c_str());
      pNode = Abc_NtkCreateObj(pNtkNetlist, ABC_OBJ_PO);
      Abc_ObjAssignName(pNode, pWord, NULL);
      pNet = Abc_NtkFindOrCreateNet(pNtkNetlist, pWord);
      Abc_ObjAddFanin(pNode, pNet);
      // 2. bind PO and it's input and.
      Node *fanin = node->fanin(0);
      if (fanin->isAnd())
      {
        Function func = best_sol_->sol_[fanin]->func();
        if (node->complement(0))
        {
          func = ~func;
          if (best_sol_->weight_[fanin] > 1) {
            Abc_ObjSetFaninC(pNode, 0);
          }
        }
        funcs[node] = func;
        if (best_sol_->weight_[fanin] == 1)
        {
          bound.insert(fanin);
        }
      }
    }

    // create internal Node.
    if (best_sol_->sol_.size() != 0)
    {
      // create node assign
      for (Node *node : nodes_)
      {
        if (bound.find(node) != bound.end())
          continue;
        if (best_sol_->weight_[node] != 0)
        {
          pCut best_cut = best_sol_->sol_[node];
          std::string exp = node->name() + " = " + best_cut->func().function();
          const std::vector<Node *> &inputs = best_cut->inputs();
          std::string true_value_hex = expToTrueValue(inputs, exp);
          strcpy(pWord, true_value_hex.c_str());
          char *pSop = Abc_SopFromTruthHex(pWord);
          // get the fanout net
          strcpy(pWord, node->name().c_str());
          pNet = Abc_NtkFindOrCreateNet(pNtkNetlist, pWord);
          assert(pNet);
          if (strcmp(pSop, " 0\n") == 0) 
          {
            Abc_Obj_t *pNodeConst0 = Abc_NtkCreateNode(pNtkNetlist);
            pNodeConst0->pData = Abc_SopRegister((Mem_Flex_t *)pNtkNetlist->pManFunc, pSop);
            Abc_ObjAddFanin(pNet, pNodeConst0);
          }
          else if (strcmp(pSop, " 1\n") == 0)
          {
            Abc_Obj_t *pNodeConst1 = Abc_NtkCreateNode(pNtkNetlist);
            pNodeConst1->pData = Abc_SopRegister((Mem_Flex_t *)pNtkNetlist->pManFunc, pSop);
            Abc_ObjAddFanin(pNet, pNodeConst1);
          }
          else
          {
            pNode = Abc_NtkCreateNode(pNtkNetlist);
            Abc_ObjAssignName(pNode, pWord, NULL);
            pNode->pData = Abc_SopRegister((Mem_Flex_t *)pNtkNetlist->pManFunc, pSop);
            Abc_ObjAddFanin(pNet, pNode);
            // connect to the fanin net
            for (int i = 0; i < inputs.size(); ++i)
            {
              strcpy(pWord, inputs[i]->name().c_str());
              pNet = Abc_NtkFindOrCreateNet(pNtkNetlist, pWord);
              assert(pNet);
              Abc_ObjAddFanin(pNode, pNet);
            }
          }
        }
      }
    }

    for (Node *po_node : Po_)
    {
      Node *fanin = po_node->fanin(0);
      strcpy(pWord, po_node->name().c_str());
      if (fanin->isConst()) // const 1
      {
        // Todo: connect const.
        pNet = Abc_NtkFindOrCreateNet(pNtkNetlist, pWord);
        assert(pNet);
        if (po_node->complement(0))
        {
          Abc_Obj_t *pNodeConst0 = Abc_NtkCreateNode(pNtkNetlist);
          char *pSop;
          pSop = Abc_SopCreateConst0((Mem_Flex_t *)pNtkNetlist->pManFunc);
          pNodeConst0->pData = Abc_SopRegister((Mem_Flex_t *)pNtkNetlist->pManFunc, pSop);
          Abc_ObjAddFanin(pNet, pNodeConst0);
        }
        else
        {
          Abc_Obj_t *pNodeConst1 = Abc_NtkCreateNode(pNtkNetlist);
          char *pSop;
          pSop = Abc_SopCreateConst1((Mem_Flex_t *)pNtkNetlist->pManFunc);
          pNodeConst1->pData = Abc_SopRegister((Mem_Flex_t *)pNtkNetlist->pManFunc, pSop);
          Abc_ObjAddFanin(pNet, pNodeConst1);
        }
        continue;
      }
      else if (fanin->isPi()) // pi
      {
        // get the fanout net
        pNet = Abc_NtkFindOrCreateNet(pNtkNetlist, pWord);
        assert(pNet);
        pNode = Abc_NtkCreateNode(pNtkNetlist);
        char *pSop;
        if (po_node->complement(0))
        {
          pSop = Abc_SopCreateInv((Mem_Flex_t *)pNtkNetlist->pManFunc);
        }
        else
        {
          pSop = Abc_SopCreateBuf((Mem_Flex_t *)pNtkNetlist->pManFunc);
        }
        pNode->pData = Abc_SopRegister((Mem_Flex_t *)pNtkNetlist->pManFunc, pSop);
        Abc_ObjAddFanin(pNet, pNode);

        // connect to the fanin net
        strcpy(pWord, fanin->name().c_str());
        pNet = Abc_NtkFindOrCreateNet(pNtkNetlist, pWord);
        Abc_ObjAddFanin(pNode, pNet);
        continue;
      }
      else if ((best_sol_->weight_[fanin] > 1)) // fanin has mult-fanout.
      {
        // get the fanout net
        pNet = Abc_NtkFindOrCreateNet(pNtkNetlist, pWord);
        assert(pNet);
        strcpy(pWord, fanin->name().c_str());
        pNode = Abc_NtkFindNode(pNtkNetlist, pWord);
        Abc_ObjAddFanin(pNet, pNode);
        continue;
      }
      else // And
      {
        if (best_sol_->weight_[fanin] == 1) {  // fanin has only one fanout, merge po and fanin.
          std::string exp = po_node->name() + " = " + funcs[po_node].function();
          const std::vector<Node *> &inputs = best_sol_->sol_[fanin]->inputs();
          std::string true_value_hex = expToTrueValue(inputs, exp);
          strcpy(pWord, true_value_hex.c_str());
          char *pSop = Abc_SopFromTruthHex(pWord);
          // get the fanout net
          strcpy(pWord, po_node->name().c_str());
          pNet = Abc_NtkFindOrCreateNet(pNtkNetlist, pWord);
          assert(pNet);
          if (strcmp(pSop, " 0\n") == 0) 
          {
            Abc_Obj_t *pNodeConst0 = Abc_NtkCreateNode(pNtkNetlist);
            pNodeConst0->pData = Abc_SopRegister((Mem_Flex_t *)pNtkNetlist->pManFunc, pSop);
            Abc_ObjAddFanin(pNet, pNodeConst0);
          }
          else if (strcmp(pSop, " 1\n") == 0)
          {
            Abc_Obj_t *pNodeConst1 = Abc_NtkCreateNode(pNtkNetlist);
            pNodeConst1->pData = Abc_SopRegister((Mem_Flex_t *)pNtkNetlist->pManFunc, pSop);
            Abc_ObjAddFanin(pNet, pNodeConst1);
          }
          else
          {
            pNode = Abc_NtkCreateNode(pNtkNetlist);
            pNode->pData = Abc_SopRegister((Mem_Flex_t *)pNtkNetlist->pManFunc, pSop);
            Abc_ObjAddFanin(pNet, pNode);
            // connect to the fanin net
            for (int i = 0; i < inputs.size(); ++i)
            {
              strcpy(pWord, inputs[i]->name().c_str());
              pNet = Abc_NtkFindOrCreateNet(pNtkNetlist, pWord);
              assert(pNet);
              Abc_ObjAddFanin(pNode, pNet);
            }
          }
        }
      }
    }
    // Io_WriteBlif( pNtkNetlist, "_temp.blif", 0, 0, 0);
    Abc_Ntk_t *pNtkLogic = Abc_NtkToLogic(pNtkNetlist);
    return pNtkLogic;
  }

  void Mapper::dumpTempNetwork()
  {
    // bind PO and it's input and.
    std::set<Node *> bound;
    std::map<Node *, Function> funcs;
    for (Node *node : Po_)
    {
      Node *fanin = node->fanin(0);
      if (fanin->isAnd())
      {
        Function func = best_sol_->sol_[fanin]->func();
        if (node->complement(0))
        {
          func = ~func;
        }
        funcs[node] = func;
        if (best_sol_->weight_[fanin] == 1)
        {
          bound.insert(fanin);
        }
      }
    }
    std::fstream dump("./_temp_.v", std::ios::out | std::ios::trunc);
    dump << "module top( ";
    for (Node *pi : Pi_)
    {
      dump << pi->name() << ", ";
    }

    dump << Po_[0]->name();
    for (int i = 1; i != Po_.size(); ++i)
    {
      dump << ", " << Po_[i]->name();
    }
    dump << " );\n";

    dump << "  input ";
    for (int i = 0; i != Pi_.size(); ++i)
    {
      dump << Pi_[i]->name();
      if (i != Pi_.size() - 1)
        dump << ", ";
      else
        dump << ";\n";
    }

    dump << "  output ";
    for (int i = 0; i != Po_.size(); ++i)
    {
      dump << Po_[i]->name();
      if (i != Po_.size() - 1)
        dump << ", ";
      else
        dump << ";\n";
    }

    if (best_sol_->sol_.size() != 0)
    {
      bool first = true;
      for (Node *node : nodes_)
      {
        if (bound.find(node) != bound.end())
          continue;
        if (best_sol_->weight_[node] != 0)
        {
          if (first)
          {
            dump << "wire " << node->name();
            first = false;
          }
          else
            dump << ", " << node->name();
        }
      }
      if (first == false)
      {
        dump << " ; \n";
      }
      // dump assign
      for (Node *node : nodes_)
      {
        if (bound.find(node) != bound.end())
          continue;
        if (best_sol_->weight_[node] != 0)
        {
          pCut best_cut = best_sol_->sol_[node];
          dump << "assign " << node->name() << " = " << best_cut->func().function() << " ;\n";
        }
      }
    }

    for (Node *po_node : Po_)
    {
      dump << "assign " << po_node->name() << " = ";
      if (po_node->fanin(0)->isConst()) // const 1
      {
        std::string str = po_node->complement(0) ? "1'b0 ;\n" : "1'b1 ;\n";
        dump << str;
        continue;
      }
      else if (po_node->fanin(0)->isPi()) // pi
      {
        if (po_node->complement(0))
        {
          dump << "~";
        }
        dump << po_node->fanin(0)->name() << ";\n";
      }
      else // And
      {
        dump << funcs[po_node].function() << ";\n";
      }
    }
    dump << "endmodule\n\n";
    dump.close();
  }

  //===----------------------------------------------------------------------===//
  //                               SimpleGate class
  //===----------------------------------------------------------------------===//
  bool SimpleGate::eat(Node *node, int idx)
  {
    bool val = false;
    Node *fanin = node->fanin(idx);
    if (node->complement(idx) == false && fanin->isPi() == false)
      val = true;
    if (fanin->fanoutNum() > 1)
    {
      val = false;
    }
    return val;
  }

  void SimpleGate::expand(int gate_size)
  {
    std::list<Node *> inputs = {root_};
		std::unordered_set<Node*> in_set;
    std::set<Node *> terminal;
    bool flag = true;
    auto itr = inputs.begin();
    while (flag == true)
    {
      Node *node = *itr;
      if (terminal.find(node) != terminal.end())
      {
        ++itr;
      }
      else
      {
        for (int i = 0; i < 2; ++i)
        {
          Node *fanin = node->fanin(i);
          if (in_set.find(fanin) != in_set.end()) {
            continue;
          }
          inputs.push_back(fanin);
					in_set.insert(fanin);
          if (eat(node, i) == false)
            terminal.insert(fanin);
        }
        inputs.erase(itr++);
				in_set.erase(node);
        internal_.push_back(node);
      }
      if (itr == inputs.end() || inputs.size() >= gate_size)
        flag = false;
    }
    for (Node *node : inputs)
    {
      inputs_.push_back(node);
    }
    internal_.erase(internal_.begin()); // remove the root form internal nodes
  }

  void SimpleGate::SimpleGateEnum(int k, bool area_oriented, std::vector<Node *> &nodes)
  {
    assert(root_->isChoice() == false);
    if (area_oriented == false)
    {
      root_->cutEnum(k, area_oriented);
      if (size() == 2)
      {
        return;
      }
    }
    else
    {
      if (size() == 2)
      {
        for (auto it = internal_.rbegin(); it != internal_.rend(); ++it)
        {
          (*it)->cutEnum(k, area_oriented);
          nodes.push_back(*it);
        }
        root_->cutEnum(k, area_oriented);
        return;
      }
    }

    // collect the inputs phase
    for (Node *node : internal_)
    {
      for (int i = 0; i != 2; ++i)
      {
        if (node->complement(i))
        {
          complemented_.insert(node->fanin(i));
        }
      }
    }

    if (root_->complement(0))
    {
      complemented_.insert(root_->fanin(0));
    }
    if (root_->complement(1))
    {
      complemented_.insert(root_->fanin(1));
    }

    std::function<bool(Node * lhs, Node * rhs)> comparator;
    if (area_oriented)
    {
      comparator = [](Node *lhs, Node *rhs)
      { return lhs->area() > rhs->area(); };
    }
    else
    {
      comparator = [](Node *lhs, Node *rhs)
      {
        if (lhs->depth() == rhs->depth())
        {
          return lhs->area() > rhs->area();
        }
        return lhs->depth() > rhs->depth();
      };
    }

    // sort the input node by area decreasing order
    std::sort(inputs_.begin(), inputs_.end(), comparator);

    // combine the input cuts
    combine(k, area_oriented);

    if (area_oriented == false)
    {
      utility::pruner<pCut, comp_pcut_delay, sizer_pcut, pcut_area> pruner(k);
      if (k == 6)
      {
        pruner.reset_store_num_upper({0, 0, 1, 2, 2, 2, 3});
      }
      else if (k == 4)
      {
        pruner.reset_store_num_upper({0, 0, 4, 6, 6});
      }
      else if (k == 5)
      {
        pruner.reset_store_num_upper({0, 0, 1, 2, 4, 5});
      }
      else
      {
        assert(0);
      }
      for (int i = 0; i != root_->cutListNum() - 1; ++i)
      {
        pruner.push(root_->getCut(i));
      }
      root_->cuts_.clear();
      for (const pDec &decom : decompositions_)
      {
        std::vector<pCut> cuts;
        decom->cutEnum(cuts, complemented_, k, area_oriented);
        for (int i = 0; i != cuts.size() - 1; ++i) // skip trivial cut
        {
          cuts[i]->setRoot(root_);
          pruner.push(cuts[i]);
        }
        nodes.insert(nodes.end(), decom->vir_nodes_.begin(), --decom->vir_nodes_.end());
        delete decom->vir_nodes_.back();
      }
      pruner.collect(root_->cuts_, area_oriented);
    }
    else
    {
      for (const pDec &decom : decompositions_)
      {
        pCut kcut = decom->kcut(root_, complemented_, area_oriented);
        root_->addCut(kcut);
        nodes.insert(nodes.end(), decom->vir_nodes_.rbegin(), decom->vir_nodes_.rend());
      }
    }

    pCut rep_cut = root_->getCut(0);
    if (area_oriented == false)
    {
      for (int i = 1; i != root_->cutListNum(); ++i)
      {
        if (rep_cut->depth() > root_->getCut(i)->depth() || (rep_cut->depth() == root_->getCut(i)->depth() && rep_cut->getArea() > root_->getCut(i)->getArea()))
        {
          rep_cut = root_->getCut(i);
        }
      }
      root_->setTimingCut(rep_cut);
    }

    int depth = rep_cut->depth() + 1;
    pCut trivial = std::make_shared<Cut>(root_, root_->minDepth()->getArea() + 1.0, depth, Encode(root_->getId()));
    root_->addCut(trivial);
    root_->setArea(root_->minDepth()->getArea() / (Area)root_->fanoutNum());

    if (area_oriented == true)
    {
      for (Node *node : internal_)
      {
        delete node;
      }
    }
    std::vector<Node *>().swap(internal_);
    std::vector<Node *>().swap(inputs_);
    std::vector<pDec>().swap(decompositions_);
    complemented_.clear();
  }

  void SimpleGate::print()
  {
    std::cout << "simple gate | ";
    std::cout << root_->getId() << " | ";
    for (Node *node : inputs_)
    {
      std::cout << node->getId();
      if (node->isPi())
        std::cout << "(" << node->name() << ")";
      std::cout << " ";
    }
    std::cout << "\n";
    for (Node *node : inputs_)
    {
      node->p("in");
    }
    for (Node *node : internal_)
    {
      node->p("internal");
    }
    root_->p("root");
    std::cout << "\n";
  }

  void SimpleGate::combine(int k, bool area_oriented)
  {
    decompositions_.reserve(1024);
    for (auto it = inputs_[0]->begin(); it != inputs_[0]->end(); ++it)
    {
      if ((*it)->cutsize() <= k)
      {
        decompositions_.emplace_back(std::make_shared<Decompose>(*it, k, size()));
      }
    }
    int combine_num = 1;
    int max_dec_size = 2 * k;
    if (area_oriented)
    {
      utility::pruner<pDec, comp_pdec_area, sizer_pdec, pdec_area> pruner(max_dec_size);
      while (combine_num != size())
      {
        Node *input = inputs_[combine_num];
        max_dec_size = k * (combine_num + 1);
        int each_size_dec_num = 4;  // the max store number in general cut merging.
        int max_dec_store_num = 10; // the max store number in the last time decompsotion pruning in wide-cut.
        pruner.reset_cell_size_upper(max_dec_size, combine_num == size() - 1 ? max_dec_store_num : each_size_dec_num);
        for (const pDec &dec : decompositions_)
        {
          for (auto it = input->begin(); it != input->end(); ++it)
          {
            pCut cut = *it;
            if (cut->cutsize() > k)
              continue;
            pDec new_dec = std::make_shared<Decompose>(*dec);
            new_dec->combine(cut);
            pruner.push(new_dec);
          }
        }
        decompositions_.clear();
        float decom_epsilon = 2.0; // the max area difference between pruning decompostions.
        float epsilon = combine_num == size() - 1 ? decom_epsilon : 0;
        pruner.collect(decompositions_, epsilon);
        ++combine_num;
      } // end while
    }
    else
    {
      utility::pruner<pDec, comp_pdec_delay, sizer_pdec, pdec_area> pruner(max_dec_size);
      while (combine_num != size())
      {
        Node *input = inputs_[combine_num];
        max_dec_size = k * (combine_num + 1);
        int each_size_dec_num = 4;  // the max store number in general cut merging.
        int max_dec_store_num = 10; // the max store number in the last time decompsotion pruning in wide-cut.
        pruner.reset_cell_size_upper(max_dec_size, combine_num == size() - 1 ? max_dec_store_num : each_size_dec_num);
        for (const pDec &dec : decompositions_)
        {
          for (auto it = input->begin(); it != input->end(); ++it)
          {
            pCut cut = *it;
            if (cut->cutsize() > k)
              continue;
            pDec new_dec = std::make_shared<Decompose>(*dec);
            new_dec->combine(cut);
            pruner.push(new_dec);
          }
        }
        decompositions_.clear();
        pruner.collect(decompositions_, false); // delay-first cuts collection
        ++combine_num;
      } // end while
    }
#ifdef _debug_
    int max_size = decompositions_.front()->input_size();
    int min_size = decompositions_.back()->input_size();

    std::sort(decompositions_.begin(), decompositions_.end(), comp_pdec_area_fn);

    Area min_cone = decompositions_.front()->area();
    Area max_cone = decompositions_.back()->area();
    std::map<pDec, int> ordered;
    for (int i = 0; i != decompositions_.size(); ++i)
    {
      ordered[decompositions_[i]] = i;
    }
#endif

    int decom_num = decompositions_.size();
    int discard_head = 0;
    int discard_tail = decom_num;

    if (area_oriented)
    {
      utility::pruner<pDec, comp_pdec_area, sizer_pdec_cutsize, pdec_area> pruner2(k);
      if (k == 6)
      {
        pruner2.reset_store_num_upper({0, 0, 1, 1, 1, 1, 3});
      }
      else if (k == 4)
      {
        pruner2.reset_store_num_upper({0, 0, 3, 4, 4});
      }
      else if (k == 5)
      {
        pruner2.reset_store_num_upper({0, 0, 3, 4, 4, 6});
      }
      else
      {
        assert(0);
      }

      for (int i = discard_head; i != discard_tail; ++i)
      {
        decompositions_[i]->area_binpack();
        pruner2.push(decompositions_[i]);
      }
      decompositions_.clear();
      pruner2.collect(decompositions_, area_oriented);
    }
    else
    {
      utility::pruner<pDec, comp_pdec_delay, sizer_pdec_cutsize, pdec_area> pruner2(k);
      if (k == 6)
      {
        pruner2.reset_store_num_upper({0, 0, 1, 2, 2, 2, 3});
      }
      else if (k == 4)
      {
        pruner2.reset_store_num_upper({0, 0, 4, 6, 6});
      }
      else if (k == 5)
      {
        pruner2.reset_store_num_upper({0, 0, 1, 2, 4, 5});
      }
      else
      {
        assert(0);
      }
      for (int i = discard_head; i != discard_tail; ++i)
      {
        pDec another_dec = decompositions_[i]->delay_binpack();
        if (another_dec)
        {
          pruner2.push(another_dec);
        }
        pruner2.push(decompositions_[i]);
      }
      decompositions_.clear();
      pruner2.collect(decompositions_, area_oriented);
    }

#ifdef _debug_
    if (size() == 8)
    {
      std::cout << "\n\n";
      std::cout << "cone = "
                << "[ " << min_cone << ", " << max_cone << " ]\t";
      std::cout << "size = "
                << "[ " << min_size << ", " << max_size << " ]\t";
      std::cout << "wcut = " << ordered.size() << "\t";
      std::cout << "gate = " << size() << "\n\n";
      for (const pDec &dec : decompositions_)
      {
        std::cout << "Area = " << dec->area() << "   In = " << dec->input_size();
        std::cout << "    Bins = " << dec->binNum() << "    Order = " << ordered[dec] << "\n";
      }
    }
#endif
  }

  //===----------------------------------------------------------------------===//
  //                               Decompose class
  //===----------------------------------------------------------------------===//
  void Decompose::print()
  {
    std::cout << "decompose cost: " << area_ << "\n";
    int i = 0;
    for (Bin *bin : bins_)
    {
      std::cout << "bin " << i++ << " : " << bin->size() << "\n";
      if (bin->cutNum())
        for (Cut *cut : bin->cuts_)
        {
          std::cout << "\t" << cut->p(false) << std::endl;
        }
    }
    std::cout << "\n";
  }

  void Decompose::area_binpack()
  {
    int k = lut_size();
    // 0. sorting the cuts by cutsize decreasing order
    std::sort(cuts_.begin(), cuts_.end(), comp_ppcut_size_greater_func);

    // 1. two-level decompose (bin-packing to generate basic boxes)
    std::vector<Bin *> &second_level_bins = bins_;
    second_level_bins.reserve(cuts_.size());
    size_t idx = 0;
    second_level_bins.push_back(new Bin(cuts_[idx]));
    std::vector<Node *> inputs;
    inputs.reserve(k);
    while (++idx != cuts_.size())
    {
      bool packed = false;
      for (Bin *bin : bins_)
      {
        Sign sign = cuts_[idx]->sign() | bin->sign_;
        if (countOnes64(sign) > k)
          continue;
        inputs.clear();
        if (utility::ordered_merge<Node *, pnode_id>(bin->inputs_, cuts_[idx]->inputs(), inputs, k) == false)
        {
          packed = true;
          bin->inputs_.swap(inputs);
          bin->cuts_.emplace_back(cuts_[idx]);
          bin->sign_ = sign;
          break;
        }
      }
      if (packed == false) // current box can't been packed into any bin, then create a new bin
      {
        second_level_bins.push_back(new Bin(cuts_[idx]));
      }
    }
    int bin_num = second_level_bins.size();

    // 2. multi-level packing
    int size = 0;
    for (const Bin *bin : bins_)
    {
      size += bin->size();
    }
    int res_num = bins_.size() - (bins_.size() * k - size); // the number of first-level bins number
    int addon = 0;
    if (res_num > 1)
      addon++;
    if (res_num > k)
      addon++;

    // the final cost after bin-packing
    area_ += (float)(bin_num + addon);

    std::sort(bins_.begin(), bins_.end(), comp_pbin_size_less);

    int first_level_cutsize = bins_.front()->size();

    // calculate cutsize
    if (addon == 0)
    {
      cut_size_ = k < (first_level_cutsize + bin_num - 1) ? k : first_level_cutsize + bin_num - 1;
    }
    else if (addon == 1)
    {
      cut_size_ = res_num;
    }
    else
    {
      cut_size_ = res_num - k + 1;
    }
  }

  pDec Decompose::delay_binpack()
  {
    pDec another_decom = nullptr;
    int k = lut_size();
    // sorting cuts by small-delay-big-cutsize ordering
    std::sort(cuts_.begin(), cuts_.end(), comp_ppcut_delay_func);
    bins_.reserve(cuts_.size());
    int idx = -1;
    std::vector<Node *> inputs;
    inputs.reserve(k);
    while (++idx != cuts_.size())
    {
      Cut *cut = cuts_[idx];
      bool packed = false;
      for (Bin *bin : bins_)
      {
        Sign sign = cut->sign() | bin->sign_;
        if (countOnes64(sign) > k)
        {
          continue;
        }
        inputs.clear();
        if (utility::ordered_merge<Node *, pnode_id>(bin->inputs_, cut->inputs(), inputs, k) == false)
        {
          packed = true;
          bin->inputs_.swap(inputs);
          bin->cuts_.emplace_back(cut);
          bin->sign_ = sign;
          break;
        }
      }
      if (packed == false)
      {
        bins_.push_back(new Bin(cut));
      }
    } // end while

    // compute delay for each bin
    std::map<int, std::vector<Bin *>> bin_map;
    for (Bin *bin : bins_)
    {
      bin->calculate_delay();
      bin_map[bin->depth()].push_back(bin);
    }

    // building multi-level tree
    int curr_level = bin_map.begin()->first;
    int critical_level = (--bin_map.end())->first;
    std::deque<Bin *> unconnected_bins;
    while (curr_level <= critical_level)
    {
      std::vector<Bin *> &curr_bins = bin_map[curr_level];
      // try to connect the unconnect bin with fanin_bins unused input
      if (unconnected_bins.size() != 0)
      {
        while (true)
        {
          Bin *wait_for_connetect = unconnected_bins.front();
          bool connect = false;
          for (Bin *sink : curr_bins)
          {
            if (sink->cutsize() < k)
            {
              sink->addConnect(wait_for_connetect);
              unconnected_bins.pop_front();
              connect = true;
              break;
            }
          }
          if (connect == false || unconnected_bins.size() == 0)
          {
            break;
          }
        }
      }
      // addon the curr_bins to unconnected bin
      for (Bin *bin : curr_bins)
      {
        unconnected_bins.push_back(bin);
      }
      ++curr_level;
    } // end while

    if (unconnected_bins.size() == 1)
    {
      assert(bin_map[critical_level].size() == 1);
      root_bin_ = bin_map[critical_level][0];
      area_ += bins_.size();
      cut_size_ = root_bin_->cutsize();
      depth_ = critical_level;
      return another_decom;
    }

    int total_fanin_num = 0;
    Bin *min_cutsize = nullptr;
    for (int i = 0; i != unconnected_bins.size(); ++i)
    {
      total_fanin_num += unconnected_bins[i]->cutsize();
      if (min_cutsize == nullptr || unconnected_bins[i]->cutsize() < min_cutsize->cutsize())
      {
        min_cutsize = unconnected_bins[i];
      }
    }
    //  when the next line's if sentence is true, then means no need to create an empty bin
    // strategy 1 : using overlying to build decomposition tree
    int overlying_cutsize = min_cutsize->cutsize() + unconnected_bins.size() - 1;
    if (overlying_cutsize <= k)
    {
      // generate another decomposition
      {
        assert(unconnected_bins.size() <= k);
        std::vector<Bin *> copy_bins;
        copy_bins.reserve(bins_.size() + 1);
        // copy the bins in this decomposition
        std::map<Bin *, Bin *> bins_map;
        for (Bin *bin : bins_)
        {
          Bin *cp_bin = new Bin(bin);
          copy_bins.push_back(cp_bin);
          bins_map[bin] = cp_bin;
        }
        for (Bin *bin : bins_)
        {
          Bin *cp_bin = bins_map[bin];
          for (Bin *fanin : bin->connect_)
          {
            cp_bin->connect_.push_back(bins_map[fanin]);
          }
        }
        another_decom = std::make_shared<Decompose>(this, copy_bins);
        // for the generated new decompose, using overlying decompose strategy to decompose it
        Bin *another_root = new Bin();
        another_root->setDepth(critical_level + 1);
        for (Bin *bin : unconnected_bins)
        {
          assert(bins_map[bin]);
          another_root->addConnect(bins_map[bin]);
        }
        another_decom->bins_.push_back(another_root);
        another_decom->root_bin_ = another_root;
        another_decom->area_ += another_decom->bins_.size();
        another_decom->depth_ = critical_level + 1;
        another_decom->cut_size_ = another_root->cutsize();
      }

      for (Bin *bin : unconnected_bins)
      {
        if (bin != min_cutsize)
        {
          min_cutsize->addConnect(bin);
        }
      }
      root_bin_ = min_cutsize;
      area_ += bins_.size();
      depth_ = critical_level + 1;
      cut_size_ = root_bin_->cutsize();
      root_bin_->setDepth(critical_level + 1);
      return another_decom;
    }

    // strategy 2 : using direct decomposition tree build
    Bin *new_bin = new Bin();
    new_bin->setDepth(critical_level + 1);
    bins_.push_back(new_bin);
    root_bin_ = new_bin;
    while (true)
    {
      Bin *wait_for_connetect = unconnected_bins.front();
      unconnected_bins.pop_front();
      if (root_bin_->cutsize() < k)
      {
        root_bin_->addConnect(wait_for_connetect);
      }
      else
      {
        Bin *root = new Bin();
        root->setDepth(root_bin_->depth() + 1);
        bins_.push_back(root);
        root->addConnect(wait_for_connetect);
        root->addConnect(root_bin_);
        root_bin_ = root;
      }
      if (unconnected_bins.size() == 0)
      {
        break;
      }
    }
    area_ += bins_.size();
    cut_size_ = root_bin_->cutsize();
    depth_ = root_bin_->depth();
    return another_decom;
  }

  void Decompose::multilevel_decompose()
  {
    int k = lut_size();
    int bin_num = bins_.size();
    // multi-level Decompose
    std::vector<Bin *> first_level_bins;
    std::vector<Bin *> &ordered_bins = bins_;
    int idx = 0;
    std::deque<Bin *> bin_deque;
    Bin *bin = ordered_bins[idx++];
    bin_deque.push_back(bin);
    first_level_bins.push_back(bin);
    while (idx != bin_num)
    {
      Bin *curr_bin = bin_deque[0];
      bin_deque.pop_front();
      int res_size = k - curr_bin->size();
      for (int i = 0; i < res_size; ++i)
      {
        if (idx != bin_num)
        {
          Bin *tmp_bin = ordered_bins[idx++];
          curr_bin->addConnect(tmp_bin);
          if (tmp_bin->size() < k)
            bin_deque.push_back(tmp_bin);
        }
        else
        {
          break;
        }
      }
      if (bin_deque.size() == 0)
      {
        for (int i = idx; i < bin_num; ++i)
        {
          first_level_bins.push_back(ordered_bins[i]);
        }
        idx = bin_num;
      }
    }
    // 3. bottom bins generation if necessary
    if (first_level_bins.size() == 1)
    {
      root_bin_ = first_level_bins[0];
    }
    else
    {
      // assert(first_level_bins.size() < 2 * k);
      int bound = first_level_bins.size() <= k ? first_level_bins.size() : k;
      Bin *bin = new Bin();
      bins_.push_back(bin);
      for (int i = 0; i < bound; ++i)
      {
        bin->addConnect(first_level_bins[i]);
      }

      if (first_level_bins.size() <= k)
      {
        root_bin_ = bin;
      }
      else
      {
        root_bin_ = new Bin();
        bins_.push_back(root_bin_);
        root_bin_->addConnect(bin);
        for (int i = bound; i != first_level_bins.size(); ++i)
        {
          root_bin_->addConnect(first_level_bins[i]);
        }
      }
    }
  }

  pCut Decompose::kcut(Node *root, const std::set<Node *> &complemented, bool area_oriented)
  {
    if (area_oriented)
    {
      multilevel_decompose();
    }
    // set the root bin's root node as gate root
    root_bin_->root_ = root;
    return root_bin_->cutGen(complemented, vir_nodes_);
  }

  void Decompose::cutEnum(std::vector<pCut> &cuts, const std::set<Node *> &complement, int lut_size, bool area_oriented)
  {
    root_bin_->cutEnum(vir_nodes_, complement, lut_size, area_oriented);
    assert(root_bin_->root_->cuts_.size() > 1);
    cuts.swap(root_bin_->root_->cuts_);
  }

  //===----------------------------------------------------------------------===//
  //                               Combination & Bin class
  //===----------------------------------------------------------------------===//
  pCut Bin::cutGen(const std::set<Node *> &complemented, std::vector<Node *> &virtual_nodes)
  {
    if (cut_)
    {
      return cut_;
    }

    if (connectSize() == 0 && cutNum() == 1) // no fanin bins and contains only a bin
    {
      root_ = cuts_[0]->root();
      cut_ = std::make_shared<Cut>(*cuts_[0]);
      return cut_;
    }

    if (root_ == nullptr)
    {
    root_ = new Node(node_counter++);
      virtual_nodes.push_back(root_);
    }
    Area area = 0;
    Function func;
    std::vector<Node *> &cut_inputs = inputs_; // now only contain cuts inputs
    for (Cut *cut : cuts_)
    {
      area += (cut->getArea() - cut->baseArea()) / (Area)cut->root()->fanoutNum();
      Function temp_func = cut->func();
      // assert(phase.find(cut->root()) != phase.end());
      if (complemented.count(cut->root()) == 1)
      {
        temp_func = ~temp_func;
      }
      func &= temp_func;
    }

    Sign sign = sign_;

    for (Bin *bin : connect_)
    {
      pCut bin_cut = bin->cutGen(complemented, virtual_nodes);
      area += (bin_cut->getArea() - 1.0) / (Area)bin->root_->fanoutNum() + 1.0;
      // Function temp_func = bin->root_->name();
	  Function temp_func = "n" + std::to_string( bin->root_->getId() );
      if (complemented.count(bin->root_) == 1)
      {
        temp_func = ~temp_func;
      }
      func &= temp_func;
      cut_inputs.emplace_back(bin->root_);
      sign |= Encode(bin->root_->getId());
    }

    area += 1.0;
    int depth = depth_ > 1 ? depth_ : 1;
    cut_ = std::make_shared<Cut>(cut_inputs, area, depth, root_, func, sign);

    if (root_->isVirtual())
    {
      root_->addCut(cut_);
      root_->setArea(cut_->getArea());
      root_->setTimingCut(cut_);
    }
    return cut_;
  }

  int Bin::calculate_delay()
  {
    int max_delay = 0;
    for (Cut *cut : cuts_)
    {
      if (cut->depth() > max_delay)
      {
        max_delay = cut->depth();
      }
    }
    depth_ = max_delay;
    return max_delay;
  }

  Node *Bin::cutEnum(std::vector<Node *> &choice_nodes, const std::set<Node *> &complement, int lut_size, bool area_oriented)
  {
    // 1. enumerate fanin bins cuts
    Node *fanin = nullptr;
    for (Bin *bin : connect_)
    {
      Node *bin_root = bin->cutEnum(choice_nodes, complement, lut_size, area_oriented);
      if (fanin == nullptr)
      {
        fanin = bin_root;
      }
      else
      {
        fanin = cutsMerge(fanin, bin_root, complement, lut_size, area_oriented);
        choice_nodes.push_back(fanin);
      }
    }

    // 2. merge the cuts of internal node of bin
    Node *other_fanin = nullptr;
    for (Cut *cut : cuts_)
    {
      if (other_fanin == nullptr)
      {
        other_fanin = cut->root();
      }
      else
      {
        other_fanin = cutsMerge(other_fanin, cut->root(), complement, lut_size, area_oriented);
        choice_nodes.push_back(other_fanin);
      }
    }

    // 3. subtree merge
    if (other_fanin && fanin)
    {
      Node *bin_root = cutsMerge(other_fanin, fanin, complement, lut_size, area_oriented);
      choice_nodes.push_back(bin_root);
      root_ = bin_root;
    }
    else if (other_fanin)
    {
      root_ = other_fanin;
    }
    else
    {
      root_ = fanin;
    }
    if (root_->isAnd())
    {
      assert(root_->cutListNum() > 1);
    }
    return root_;
  }

  Node *Bin::cutsMerge(Node *fanin1, Node *fanin2, const std::set<Node *> &complement, int lut_size, bool area_oriented)
  {
    Node *node = new Node(node_counter++);
    node->setFanoutNum(1);
    node->setAig(fanin1, fanin2, complement.count(fanin1) == 1, complement.count(fanin2) == 1);
    node->cutEnum(lut_size, area_oriented);
    return node;
  }

} // end namespace
