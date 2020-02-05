import React, {ChangeEvent, memo, ReactElement, useEffect, useState} from "react";
import Paper from "@material-ui/core/Paper";
import Button from "@material-ui/core/Button";
import Checkbox from "@material-ui/core/Checkbox";
import FormControlLabel from "@material-ui/core/FormControlLabel";
import "./SelectMenu.scss"
import Typography from "@material-ui/core/Typography";
import CheckBoxOutlineBlankOutlinedIcon from '@material-ui/icons/CheckBoxOutlineBlankOutlined';
import CheckBoxOutlinedIcon from '@material-ui/icons/CheckBoxOutlined';
import IndeterminateCheckBoxOutlinedIcon from '@material-ui/icons/IndeterminateCheckBoxOutlined';
import {propTypes} from "./propTypes";
import VirtualList from "react-tiny-virtual-list";
import {Item, MultipleMenu} from "../../interface";

function SelectMultiple({cancelHandler, applyHandler, items, open}: MultipleMenu): ReactElement {
  const [list, setList] = useState<Item[]>([]);
  const [allState, setAllState] = useState<Item>({label: 'All', value: null, checked: false, indeterminate: false});

  useEffect(() => {
    const checked = items.every(state => state.checked);

    const all = {label: 'All', checked, value: null, indeterminate: items.some(state => state.indeterminate)};

    setAllState(all);
    setList(items);
  }, [items]);

  useEffect(() => {
    if (list) {
      const checked = list.every(state => state.checked);

      const all = {
        label: 'All',
        checked,
        value: null,
        indeterminate: !checked ? list.some(state => state.checked) : false
      };
      setAllState(all);
    }
  }, [list]);

  const handleChange = (event: ChangeEvent<HTMLInputElement>) => {
    const current_id = event.target.value;

    setList(prev => prev.map(item => item.id === current_id
      ? {
        ...item,
        checked: !item.checked
      }
      : item
    ));
  };

  const handleChangeAll = () => {
    setList(prev => prev.map(item => ({
      ...item,
      indeterminate: false,
      checked: !allState.checked
    })));
  };

  const handleAccept = () => {
    applyHandler(list.filter(item => item.checked));
    cancelHandler();
  };

  return (<>
    {open && !!list.length && <Paper className={`popperWrapper popperWrapper`}>
      <div>
        <FormControlLabel
          classes={{root: "labelRoot", label: "text"}}
          control={<Checkbox
            classes={{root: "checkboxRoot"}}
            checked={allState.checked}
            indeterminate={allState.indeterminate}
            onChange={handleChangeAll}
            checkedIcon={<CheckBoxOutlinedIcon fontSize="small"/>}
            indeterminateIcon={<IndeterminateCheckBoxOutlinedIcon fontSize="small"/>}
            icon={<CheckBoxOutlineBlankOutlinedIcon fontSize="small"/>}
            value={allState.value}
          />}
          label={<Typography noWrap className="text" variant="body2">{allState.label}</Typography>}
        />
        <VirtualList
          width='100%'
          height={140}
          itemCount={list.length}
          itemSize={28}
          renderItem={({index, style}) => {
            const item = list[index];

            return (<FormControlLabel
              style={style}
              key={index}
              classes={{root: "labelRoot", label: "text"}}
              control={<Checkbox checked={item.checked}
                                 classes={{root: "checkboxRoot"}}
                                 onChange={handleChange}
                                 checkedIcon={<CheckBoxOutlinedIcon fontSize="small"/>}
                                 icon={<CheckBoxOutlineBlankOutlinedIcon fontSize="small"/>}
                                 value={item.id}/>}
              label={<Typography noWrap className="text" variant="body2">{item.label}</Typography>}
            />)
          }
          }
        />
      </div>
      <div className="popperWrapperActions">
        <div className="m-r-xs">
          <Button
            onClick={() => {
              cancelHandler();
            }}
            variant="contained"
            size="small">
            cancel
          </Button>
        </div>
        <Button
          onClick={handleAccept}
          variant="contained"
          size="small"
          color="secondary"
        >Apply
        </Button>
      </div>
    </Paper>}
  </>);
};

SelectMultiple.propTypes = propTypes();

export default memo(SelectMultiple);
