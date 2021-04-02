
size_t
get_l1_line_sz (void)
{
	FILE * p = NULL;
	unsigned sz = 0;

	p = fopen(L1_LINE_SZ_PATH, "r");
	if (!p) {
		perror("Couldn't open linux cache descriptor file\n");
		return 0;
	}

	fscanf(p, "%d", &sz);
	fclose(p);
	return sz;
}
