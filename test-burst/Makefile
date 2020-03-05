MPL?=../build/bin/mpl

NAMES=elastic elastic-wake-next blocking-elastic nonelastic 

all: $(NAMES)
.PHONY: clean $(NAMES)

$(NAMES):
	$(MPL) -default-type int64 $@.mlb

clean:
	rm -f $(NAMES)

# elastic-wake-next:
# 	$(MPL) -default-type int64 elastic-wake-next.mlb
# 
# blocking-elastic:
# 	$(MPL) -default-type int64 blocking-elastic.mlb
# 
# nonelastic:
# 	$(MPL) -default-type int64 nonelastic.mlb
