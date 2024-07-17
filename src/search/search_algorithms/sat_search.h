#ifndef SEARCH_ALGORITHMS_EAGER_SEARCH_H
#define SEARCH_ALGORITHMS_EAGER_SEARCH_H

#include "../search_algorithm.h"

#include <memory>
#include <vector>


namespace plugins {
class Feature;
}

namespace sat_search {
class SATSearch : public SearchAlgorithm {
	int planLength;
	int currentLength;

protected:
    virtual void initialize() override;
    virtual SearchStatus step() override;

public:
    explicit SATSearch(const plugins::Options &opts);
    virtual ~SATSearch() = default;

    virtual void print_statistics() const override;
};

extern void add_options_to_feature(plugins::Feature &feature);
}

#endif
